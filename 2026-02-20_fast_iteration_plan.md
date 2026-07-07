# Plan: Fast-iteration InsertSpec.v insert_ok Proof
Updated: 2026-02-20

## Problem

The `insert_ok` proof in `InsertSpec.v` takes 15-20 minutes to rebuild,
making iteration on the remaining admit (step 10) impractical.

**Two root causes:**

1. **6x branch overhead** — `wp_nd_args` generates 6 branches (3! argument
   orderings for `ins(k, v, n)`). Every subsequent `all:` tactic runs 6x.
   Steps 5-8 contain ~10 heavy tactic sequences, each on all 6 branches.

2. **AST loading + vm_compute overhead** — `Require Import map_int_int_cpp`
   loads the 96K-line AST (6.7 MB `.vo`). Six `vm_compute; reflexivity`
   lookup proofs each scan the full symbol table. Together these add
   several minutes before the actual proof tactics even start.

## Solution: Three-layer file split

### Layer 1: `InsertDefs.v` (compile once, ~5-10 min)

Extract everything that requires the AST or expensive computation:

- `Require Import map_int_int_cpp`
- Function name definitions (`insert_name`, `ins_name`, etc.)
- Function extraction (`insert_func`, `ins_func`, etc.)
- Symbol table lookup proofs (6 × `vm_compute; reflexivity`)
- Spec definitions (`insert_spec`, `ins_spec`, etc.)
- Admitted callee proofs (`ins_ok`, `makeCopy_ok`, etc.)
- Helper lemmas (`ins_has_body`, `black_lookup`)

This file is compiled ONCE via `make`. The resulting `InsertDefs.vo`
caches all `vm_compute` results. It only needs rebuilding when specs
or function definitions change.

### Layer 2: `InsertSpec.v` (main proof, ~10-12 min)

Imports `InsertDefs.v` (no re-running vm_compute). Contains:

- `insert_ok_post_call` helper lemma (steps 5-10, **1 branch**)
- `insert_ok` main proof (steps 1-4 on 6 branches + `iApply` helper)

The helper lemma eliminates the 6x overhead: steps 5-10 compile once,
then `iApply` applies cheaply in all 6 branches.

Still loads the AST transitively (via `InsertDefs.vo`), but doesn't
re-run any `vm_compute` lookups.

### Layer 3: `InsertStep10.v` (scaffolding, **~30 seconds**)

Development scaffolding for step 10 — does NOT import the AST at all:

- Only imports `Tactics.v`, `RBTree.v`, `TreeRep.v`
- Contains `insert_step10_proof` — a standalone lemma proving the
  step 10 Iris entailment (destroy local + postcondition)
- **No AST loading, no vm_compute, no 6-branch overhead**

### Why step 10 is AST-independent

After step 8's `repeat wp_step` fully processes the C++ AST, the
remaining goal is expressed entirely in BRiCk primitives:

- `wp_destroy_prim` (destroy local variable)
- `tptstoR` / `tptsto_fuzzyR` (points-to assertions)
- `treeR` (tree representation — from TreeRep.v, not the AST)
- `anyR` (parameter cleanup)
- The postcondition wand from `insert_spec`

None of these reference the generated AST. So step 10 can be developed
in a file that never loads `map_int_int_cpp.vo`.

## Iteration workflow

```
Edit InsertStep10.v  →  build (~30 sec)  →  check  →  repeat
                              ↓ (when done)
                    Paste proof into InsertSpec.v
                              ↓
                    Final build (~10-12 min)
```

## Getting the goal types (one-time cost)

To define the scaffolding lemma, we need the exact goal type and
hypothesis types at the start of step 10. Two approaches:

**Option A: Build with `idtac` goal printing** (~15-20 min one-time)

Add after step 8 (replacing step 10):
```coq
all: Set Printing All;
     match goal with |- ?G => idtac "=== GOAL ===" G end;
     Unset Printing All;
     admit.
```

Build InsertSpec.v once. The `idtac` output shows the exact goal.
Simultaneously, print the Iris context with individual hypothesis
inspections.

**Option B: Infer from the proof code** (no build required)

The step 10 proof code already tells us the shapes:
- Destroy side: `wp_destroy_prim.unlock` → `(∃ v, tptstoR ...) ∗ ▷ K`
- Cont side: After `iNext`, `iApply ("Hcont" $! curr with "[Htree]")`

We know the hypothesis types from the proof:
- `Hcurr_local`: `tptsto_fuzzyR (Tptr _Node) (cQp.m 1) (Vptr curr)`
- `Htree`: `treeR (cQp.m 1) (RBTree.insert k v t)`
- `Hpk/Hpv/Hpn`: `tptsto_fuzzyR` for parameters
- `Hcont`: derived from `insert_spec`'s `cpp_spec` expansion

The risk is getting the cont goal wrong (it depends on how BRiCk
structures the Kfree/Kreturn chain). If the scaffolding lemma's type
doesn't match, the error will tell us what's needed — and fixing it
in the scaffolding file only takes ~30 seconds per attempt.

**Recommendation: Option B first, fall back to Option A if stuck.**

## Implementation order

1. **Create `InsertDefs.v`**: Move function defs, lookups, specs out
   of InsertSpec.v. Add Makefile rule. Compile once.

2. **Create `InsertStep10.v`**: Write standalone lemma for step 10
   using inferred types (Option B). Iterate until it compiles (~30 sec
   per attempt).

3. **Create `insert_ok_post_call` helper in InsertSpec.v**: Move
   steps 5-10 into the helper (1 branch). Wire `insert_ok` to use
   `all: iApply insert_ok_post_call`.

4. **Slim down `InsertSpec.v`**: Import `InsertDefs.v` instead of
   the raw AST. Contains only the proofs.

5. **Full `make proofs`** to verify everything compiles together.

## Step 10 proof (the actual admit)

Based on FindSpec.v's return pattern and the `wp_destroy_local` tactic:

**Destroy side** (tptsto_fuzzyR → tptstoR):
```coq
rewrite wp_destroy_prim.unlock /=;
iModIntro;
iSplitL "Hcurr_local";
[ iRevert "Hcurr_local"; rewrite _at_tptsto_fuzzyR;
  iIntros "_dtmp";
  iDestruct "_dtmp" as (?) "[% _dtpsto]";
  iExists _; rewrite _at_tptstoR; iExact "_dtpsto"
```

**Cont side** (postcondition application, following FindSpec.v):
```coq
| iNext;
  iApply ("Hcont" $! curr with "[Htree]");
  [ iExact "Htree"
  | iFrame "Hret_store";
    iSplitL "Hpk"; [wp_finish_anyR |];
    iSplitL "Hpv"; [wp_finish_anyR | wp_finish_anyR] ] ].
```

Note: the anonymous `iIntros "?"` in step 8 may need to be changed to
`iIntros "Hret_store"` so we can reference it in step 10.

## Build time estimates

| Scenario                     | Time        |
|------------------------------|-------------|
| Current (full rebuild)       | 15-20 min   |
| InsertStep10.v scaffolding   | ~30 sec     |
| InsertSpec.v (with helpers)  | ~10-12 min  |
| InsertDefs.v (one time)      | ~5-10 min   |

## Files to create/modify

- **Create** `coq/InsertDefs.v` — function defs, lookups, specs
- **Create** `coq/InsertStep10.v` — scaffolding for step 10
- **Modify** `coq/InsertSpec.v` — slim down, add helper, import defs
- **Modify** `Makefile` — add rules for new .vo files
- **Modify** `_CoqProject` (if it exists) — add new files
