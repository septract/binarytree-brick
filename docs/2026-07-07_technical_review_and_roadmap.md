# Technical Review & Roadmap — Daedalus RB-Tree BRiCk Verification

*Date: 2026-07-07*

> **Snapshot note (2026-07-12).** This is a dated review; the *rationale and
> dependency graph* below are still current, but the concrete file list and
> per-file status have moved on. Notably `RebalanceSpec.v` has since been split
> into `RebalanceDefs.v` + `SetRebalanceLeft.v` + `SetRebalanceRight.v` (for
> build performance), and the no-rotation cases of both rebalance functions are
> now proved. For the live status and "start here" pointer, read `TODO.md`
> (top section) and `README.md`'s proof-status table first.

A soundness/structure review of the Rocq proof development, plus a roadmap to
a complete proof of the Daedalus C++ red-black tree (`cpp/ddl/map.h`).

---

## Part 1 — Soundness & structure review

### 1.1 Overall verdict

The development is **sound in the parts that are complete**, and the
architecture is well-chosen. The functional model (`RBTree.v`) and the
`findNode` refinement (`FindSpec.v`) are genuinely closed — no `admit`, no
project-level `Axiom` — resting only on BRiCk's own axiom base plus two
clearly-documented framework gaps (see §1.4). The remaining operations
(`insert` callees, ref-counting) are scaffolded with honest `admit`s and
correct-looking spec statements.

The verification strategy is the standard, correct one: a pure functional
spec proved to preserve the RB invariants, a separation-logic representation
predicate (`treeR`) linking it to the C++ heap, and per-function refinement
proofs, composed by a glue theorem.

### 1.2 What is actually proved (trustworthy today)

| Item | File | Status |
|---|---|---|
| Functional RB-tree: `ins`/`insert`/`findNode`, `IsBST`/`NoRedRed` preservation, `fromList` invariants, `findNode` correctness | `RBTree.v` | **Complete** (41 `Qed`, 0 admit) |
| `treeR` representation predicate + unfolding lemmas | `TreeRep.v` | **Complete** |
| `findNode` C++ refinement (`findNode_ok`) | `FindSpec.v` | **Complete** (0 admit) |
| Tree-specific tactic lemmas (`treeR_node_*`, etc.) | `Tactics.v` | **Complete** |
| `insert_ok` (top-level, *modulo* `ins_ok`) | `InsertSpec.v` | **Complete proof, admitted callee** |

`insert_ok` is a real, closed `Qed` — it fully discharges `Node::insert`'s
body (`curr = ins(...); curr->color = black; return curr`) against
`insert_spec`, assuming only `ins_ok` (which it calls). That is exactly the
right decomposition; the only thing missing beneath it is `ins_ok` itself.

### 1.3 The functional model faithfully mirrors the C++

I checked `RBTree.v` against `cpp/ddl/map.h` line by line:

- `ins` (RBTree.v:95) matches `Node::ins` (map.h:133): `k<key` →
  `setRebalanceLeft c (ins k v l) …`; `key<k` → `setRebalanceRight …`;
  equal → value update in place (`n->value = v`). ✓
- `setRebalanceLeft`/`setRebalanceRight` (RBTree.v:54, 73) match the LL/LR
  and RL/RR rotation logic in map.h:155 / 201, including that rotation only
  fires when `is_black(n) && is_red(newLeft)`. ✓
- `insert = makeBlack ∘ ins` matches `insert` setting `curr->color = black`. ✓
- `findNode` (RBTree.v:121) matches the iterative `Node::findNode` loop. ✓
- Colors: `Red=true`, `Black=false` — matches `map.h:32-33`. ✓

This 1:1 correspondence is the crux of the whole effort, and it holds.

### 1.4 Trusted base — the two BRiCk framework gaps

`WpTactics.v` contains **exactly two** genuine `admit`s
(`wp_fptr_of_func_ok_compat` nearby is *proved*, `Qed`):

1. **`wp_operand_cfun2ptr_global`** — resolving a function-pointer cast
   (`Ecast Cfun2ptr (Eglobal …)`) needs `align_of (Tfunction …)`, which BRiCk
   declares as a `Parameter` with no axiom. Blocks every *direct* C++ call.
2. **`wp_operand_read_global_const`** — reading a global `const`
   (`Node::black`) needs `initializedR`, but BRiCk's `initSymbol` returns
   `emp` (static initialization "not yet supported", per an upstream TODO).

Both are **semantically valid and acknowledged upstream**, and both are stated
as `Lemma … Admitted` (deferred obligations), *not* `Axiom`. They are the
honest, minimal trusted surface.

> **Recommendation:** These two should be surfaced explicitly in the README's
> proof-status section and tracked as upstream BRiCk issues. They are the only
> non-obvious things a reviewer must trust. Note `findNode_ok` does **not**
> depend on #1 (findNode makes no calls) — it is the cleanest result in the repo.

### 1.5 Spec-design observations (the important soundness questions)

**(a) The ownership story for `ins`/`makeCopy` is the key open risk.**
`ins` does `n = makeCopy(n)` — copy-on-write. `makeCopy` (map.h:119) returns
`p` unchanged if `ref_count==1`, else allocates a fresh `Node(p)` whose
constructor does `copy(left); copy(right)` — i.e. **shares children and bumps
their ref-counts**. But every spec uses `treeR (cQp.m 1) t` with an
**existentially-quantified `ref_count`** (TreeRep.v:110) and *unique*
(fraction 1) ownership of the whole tree.

This is *sound for functional correctness* as written, because `ins_spec`
consumes `n |-> treeR 1 t` and produces `ret |-> treeR 1 (ins k v t)` — the
"unique-ownership" reading. It models the caller-facing contract (`ins` "owns
n", returns an "owned unique node"). The subtlety: proving `ins_ok` will
require `makeCopy_spec` to actually *produce* a unique `treeR 1` tree from a
possibly-shared input, which is only true because the caller passed unique
ownership in. `makeCopy_spec` (InsertDefs.v:231) states exactly this
(`p |-> treeR 1 t` ⊢ `ret |-> treeR 1 t`), so the specs compose — but the
*proof* of `makeCopy_ok` is where real ref-count reasoning (ghost state) will
be needed, and it is deferred to Phase 6. **This is consistent, not a bug**,
but it means `treeR 1` currently bakes in "single-threaded unique ownership";
sharing is not yet modeled. That is fine for `insert`-only correctness and
should be stated as an explicit assumption.

**(b) `setRebalance*_spec` uses field-level ownership, not `treeR`, at `n`.**
(InsertDefs.v:259) This is deliberate and correct: after `ins(k,v,n->left)`
consumes the left subtree, the caller holds `n`'s fields + right subtree + the
new left tree, *not* a whole `treeR n`. The spec mirrors that state precisely.
The `\pre` existentially binds the stale `lp` (never read — every path
overwrites `n->left`). Well-designed.

**(c) `is_black`/`is_red` specs use `option Color`** to fold the null case
(null ⇒ black) into one spec (InsertDefs.v:311). Matches `map.h:90`. Good.

**(d) `ref_count` is existential in `treeR`.** Correct for functional specs
(the count is bookkeeping invisible to functional behavior), but it means
`treeR` cannot by itself state memory-safety claims. Those need the separate
ref-count discipline (RefCount.v / Phase 6).

### 1.6 Structural / hygiene notes

- **`RefCount.v` is prose only** (0 definitions, all comments). It is a design
  sketch, not a proof. Fine as a placeholder, but it should be labeled clearly
  (and its `\pre/\post` sketches are pseudo-syntax, not Coq). Consider renaming
  to `RefCount_sketch.v` or moving the prose to `docs/` until Phase 6.
- **`Invariants.v` is a scaffold** with two trivial lemmas (`isBST_empty`,
  `noRedRed_empty`) and a commented-out capstone. Honest, but the "top-level
  correctness theorem" does not exist yet.
- **`RebalanceSpec.v` / `InsSpec.v`** are well-structured skeletons: the case
  analysis exactly mirrors the functional definitions, with `admit` at each
  leaf. Good scaffolding — the hard work (BRiCk `Eseqand`, `Enew`+constructor,
  Löb recursion through `IH`) is isolated and documented.
- **Naming collision:** `is_black`/`is_red` are defined both in `RBTree.v`
  (functional, on `tree`) and referenced as C++ specs — no actual conflict
  (different types) but worth a comment.

### 1.7 Bottom line

Nothing is unsound. The completed pieces are genuinely closed on a small,
honest, documented trusted base. The gap to "fully verified" is entirely in
the `insert` write-path (rotations, recursion, allocation) and the ref-count
memory-safety layer — all correctly scaffolded, none started-and-broken.

---

## Part 2 — Roadmap to a complete proof

The goal: **`Node::insert` and `Node::findNode` fully verified**, composed into
a top-level correctness + memory-safety theorem for `DDL::Map<int,int>`.
Ordered by dependency and by unlocking-value.

### Phase A — Enable direct C++ calls (unblocks everything with a callee)

**A1. Discharge or quarantine the two BRiCk gaps (`WpTactics.v`).**
- Preferred: get the fixes upstreamed (function alignment; static-init
  support) and pin the BRiCk commit that includes them, then close the two
  `admit`s. This is the single highest-leverage item — it removes the entire
  trusted surface beyond BRiCk's own axioms.
- Interim: if upstream is slow, promote them from `Admitted Lemma` to a single
  clearly-marked `Axiom` block in one file (`Trusted.v`) with a printed
  `Print Assumptions` audit, so the trusted base is visible in one place.
- *Effort:* days (interim) / upstream-dependent (real fix).
- *Unlocks:* `is_black`/`is_red` calls, `makeCopy` call, recursive `ins`.

### Phase B — Leaf operations (`is_black`, `is_red`)

**B1. Prove `is_black_ok`, `is_red_ok`** (`InsertDefs.v` specs already stated).
These are tiny (single null-check + field read), read-only, and are the first
real use of direct calls. Doing them first validates the call machinery from
Phase A on the simplest possible callee.
- *Depends on:* A1.
- *Effort:* 1-2 days once A1 lands.

### Phase C — Rotations (`setRebalanceLeft_ok`, `setRebalanceRight_ok`)

**C1. Fill in `RebalanceSpec.v`'s 20 `admit`s.** The scaffold is done; each
case needs: handle the `Eseqand` short-circuit condition
(`is_black(n) && is_red(newLeft)`), follow the AST path, and fold the result
into `treeR (setRebalanceLeft …)`. The default-case pure lemmas
(`setRebalanceLeft_default`) are already proved.
- Key new patterns: `Eseqand` evaluation, calling `is_red`/`is_black` (from B),
  in-place field writes (`newLeft->left = l`), `makeCopy` on a subtree (uses D).
- *Depends on:* B1, and `makeCopy_ok` (D1) for the rotation bodies that copy
  `sub2`. Consider proving the **default/no-rotation cases first** (no
  `makeCopy`), which need only B1.
- *Effort:* 1-2 weeks — this is the most intricate wp work (many field
  permutations).

### Phase D — Copy-on-write (`makeCopy_ok`) + ref-count model

**D1. Design the ref-count ghost state and prove `makeCopy_ok`.** This is the
conceptual heart of memory reasoning. Requires:
- A ghost CMRA tracking per-node ownership tokens (RefCount.v sketch).
- Deciding how `treeR` relates to shared ownership: either (i) keep `treeR 1`
  as "unique/owned" and prove `makeCopy` re-establishes uniqueness by deep-copy
  when `ref_count>1`, or (ii) generalize `treeR` to fractional/shared trees.
  Recommend (i) first — it matches the current specs and the "owns n" contract,
  and defers fractional sharing.
- The `new Node(p)` copy-constructor path (`Enew` + constructor + `copy`
  children) must be verified.
- *Depends on:* A1 (constructor calls), decision on the ownership model.
- *Effort:* 2-4 weeks (the ghost-state design is the gating task).

### Phase E — Recursive insert (`ins_ok`)

**E1. Complete the Löb-induction proof in `InsSpec.v`.** Scaffold + strategy
are in place (`iLöb as "IH"`, `wp_call_from_hyp` for the recursive call). Needs:
- Base case: `Enew Node(red,nullptr,k,v,nullptr)` → `treeR (Node Red Leaf …)`
  (shares the constructor work with D1).
- Recursive case: `makeCopy` (D1), read `n->key`, branch, recursive `ins` via
  `IH`, then `setRebalance*` (C1), value-update case.
- *Depends on:* C1, D1, B1 (all callees), A1.
- *Effort:* 1-2 weeks once callees land. Then `insert_ok` is already done, so
  **`Node::insert` becomes fully verified** at this point.

### Phase F — Memory safety (`free`, `copy`, leak-freedom)

**F1. Specify and prove `Node::free` and `Node::copy`** against the ref-count
ghost state, establishing: no double-free, no use-after-free, and that a tree
with unique ownership is fully reclaimed. This is what makes the ref-count
model pay off beyond functional correctness.
- *Depends on:* D1 (ghost state).
- *Effort:* 2-3 weeks.

### Phase G — Top-level composition (`Invariants.v`)

**G1. State and prove the capstone.** Compose: C++ `insert` refines functional
`insert` (E) + `insert` preserves `IsBST`/`NoRedRed` (RBTree.v, done) + C++
`findNode` refines functional `findNode` (done) + ref-count soundness (F) into:
*"any `Map<int,int>` built by `insert`s from empty is a memory-safe BST with
O(log n) lookup, and `findNode`/`contains`/`lookup` return the correct value."*
- Also fold in a **black-height/balance** functional lemma if a strong height
  bound is wanted (currently `NoRedRed` + rotation structure imply it, but a
  standalone `validAux`-based theorem would make it explicit).
- *Depends on:* E, F.
- *Effort:* 1 week.

### Optional / stretch

- **`Map::contains` / `Map::lookup` / `Map` constructor** wrappers (thin
  wrappers over `findNode`; easy once `findNode_ok` composes).
- **`Node::valid`** runtime checker: prove it returns `>0` iff `IsBST ∧
  NoRedRed ∧ uniform-black-height`. Nice-to-have, self-contained.
- **`Iterator`** (in-order traversal with a heap-allocated parent chain) —
  substantial separate effort; probably out of scope.
- **Delete** — the Daedalus C++ has no delete, so the Lean `DoubleBlack`
  deletion model is *not* needed for C++ verification (it's a companion
  experiment). Out of scope for this repo's goal.

### Suggested order & critical path

```
A1 (BRiCk gaps) ─┬─> B1 (is_black/red) ─┬─> C1 (rotations) ──┐
                 └─> D1 (makeCopy + ghost state) ────────────┼─> E1 (ins_ok) ─> [insert done] ─┐
                                          └─> F1 (free/copy, memory safety) ───────────────────┴─> G1 (capstone)
```

**A1 is the gate.** After it, B/C/D can proceed largely in parallel; E depends
on all three; F depends on D; G depends on E+F. The functional layer (RBTree.v)
and `findNode` are already done, so they contribute no risk to the critical path.

### Rough sizing

| Phase | Effort (focused) | Risk |
|---|---|---|
| A — BRiCk gaps | days (interim) / upstream (real) | Medium (upstream dependency) |
| B — is_black/red | 1-2 days | Low |
| C — rotations | 1-2 weeks | Medium (intricate wp) |
| D — makeCopy + ghost state | 2-4 weeks | **High** (design-gated) |
| E — ins_ok | 1-2 weeks | Medium |
| F — memory safety | 2-3 weeks | High |
| G — capstone | 1 week | Low |

The **functional-correctness milestone** (`insert` + `findNode` verified,
capstone modulo memory safety) is reachable via A→B→C→D→E→(partial G). The
**full memory-safety milestone** adds D(full)→F→G.
