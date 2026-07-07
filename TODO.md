# TODO / Backlog

Backlog for completing the BRiCk verification of the Daedalus red-black tree
(`cpp/ddl/map.h`). For the narrative rationale, dependency graph, and effort
sizing, see [`docs/2026-07-07_technical_review_and_roadmap.md`](docs/2026-07-07_technical_review_and_roadmap.md).

Status legend: `[ ]` todo · `[~]` in progress · `[x]` done · `[!]` blocked

---

## Done (do not regress)

- [x] Functional model `RBTree.v` — `ins`/`insert`/`findNode`, `IsBST`/`NoRedRed`
      preservation, `fromList` invariants, `findNode` correctness (0 admit).
- [x] Representation predicate `treeR` + unfolding lemmas (`TreeRep.v`).
- [x] `findNode_ok` — C++ `findNode` refinement (`FindSpec.v`, 0 admit).
- [x] `insert_ok` — C++ `insert` refinement *modulo* `ins_ok` (`InsertSpec.v`).
- [x] Reproducible build (`make setup`, pinned toolchain, `BUILDING.md`).

---

## Phase A — Enable direct C++ calls  `[!]` gate for everything below

The two BRiCk framework gaps in `WpTactics.v` block all direct function calls
and global-const reads. Highest-leverage item.

- [ ] **A1a** File upstream BRiCk issues for both gaps, referencing
      `docs/brick-framework-gaps.v`:
  - [ ] function alignment: `align_of (Tfunction …)` has no axiom
        (blocks `wp_operand_cfun2ptr_global`).
  - [ ] static initialization: `initSymbol` returns `emp`
        (blocks `wp_operand_read_global_const`).
- [ ] **A1b** Interim: consolidate the two `Admitted` lemmas into a single
      `Trusted.v` with a header explaining they are BRiCk gaps, and add a
      `Print Assumptions` audit target to the Makefile so the trusted base is
      visible in one place.
- [ ] **A1c** Real fix: once upstream lands, pin the new BRiCk commit in
      `scripts/pins.env`, close both `admit`s, re-run `make proofs`.
- [ ] **A1d** Update README proof-status to name the trusted base explicitly
      (and note `findNode_ok` does not depend on it).

## Phase B — Leaf operations  (depends: A1)

Smallest real callees; validate the call machinery.

- [ ] **B1a** Prove `is_black_ok` (`InsertDefs.v` spec already stated):
      null-check + `n->color` read, return `option Color` result.
- [ ] **B1b** Prove `is_red_ok` (negation of `is_black`; same ownership).
- [ ] **B1c** Factor any shared "read `_color` field via const ptr" tactic
      into `Tactics.v`.

## Phase C — Rotations  (depends: B1; rotation bodies also need D1)

Fill in `RebalanceSpec.v` (currently 20 `admit`s, scaffold complete).

- [ ] **C1a** `setRebalanceLeft_ok`: handle `Eseqand` short-circuit for the
      `is_black(n) && is_red(newLeft)` guard.
- [ ] **C1b** Prove the **default / no-rotation** cases first (need only B1,
      no `makeCopy`): `c=Red`; `newL=Leaf`; `newL=Node Black …`;
      `newL=Node Red (non-Red) _ (non-Red)`.
- [ ] **C1c** LL rotation case (copies `sub2` → needs D1).
- [ ] **C1d** LR rotation case (copies `sub2` → needs D1).
- [ ] **C1e** `setRebalanceRight_ok`: mirror of C1a–C1d (RL/RR).
- [ ] **C1f** Establish reusable tactics for in-place field writes
      (`n->left = …`, `n->color = black`) in `Tactics.v`.

## Phase D — Copy-on-write + ref-count model  `[!]` design-gated, high risk

The conceptual heart of memory reasoning; gates `ins_ok` and memory safety.

- [ ] **D1a** Decide the ownership model. Recommended: keep `treeR (cQp.m 1)`
      as "unique/owned" and prove `makeCopy` re-establishes uniqueness by
      deep-copy when `ref_count>1` (defer fractional/shared trees).
      Document the decision in `TreeRep.v`.
- [ ] **D1b** Define the ref-count ghost-state CMRA (replace the prose in
      `RefCount.v` with real Coq; consider renaming the sketch out of the
      build until then).
- [ ] **D1c** Verify the `new Node(p)` copy-constructor path
      (`Enew` + constructor + `copy(left)/copy(right)`).
- [ ] **D1d** Prove `makeCopy_ok` against `makeCopy_spec` (InsertDefs.v:231).

## Phase E — Recursive insert  (depends: A1, B1, C1, D1)

Complete `InsSpec.v` (Löb-induction scaffold in place).

- [ ] **E1a** Base case: `n == nullptr` → `Enew Node(red,nullptr,k,v,nullptr)`
      → `treeR (Node Red Leaf k v Leaf) = ins k v Leaf`.
- [ ] **E1b** Step through the `n == nullptr` comparison (false branch) and
      `n = makeCopy(n)`.
- [ ] **E1c** Read `n->key`, case-split `k <? kn`.
- [ ] **E1d** `k < kn`: read `n->left`, recursive `ins` via `wp_call_from_hyp
      "IH"`, then `setRebalanceLeft` with field-level ownership.
- [ ] **E1e** `kn < k`: mirror with `setRebalanceRight`.
- [ ] **E1f** `k = kn`: skip the two `constexpr false` `hasRefs` branches,
      write `n->value = v`, fold `treeR (Node c l kn v r)`.
- [ ] **E1g** Close `ins_ok`; ⇒ **`Node::insert` fully verified** (insert_ok
      already done).

## Phase F — Memory safety  (depends: D1)

- [ ] **F1a** Spec + prove `Node::free`: decrement, and on last ref recurse
      into children + `delete` (no double-free, no use-after-free).
- [ ] **F1b** Spec + prove `Node::copy` (increment ref-count).
- [ ] **F1c** Leak-freedom: a uniquely-owned tree is fully reclaimed.

## Phase G — Top-level composition  (depends: E, F)

Turn `Invariants.v` from scaffold into the capstone.

- [ ] **G1a** State the top-level theorem: a `Map<int,int>` built by `insert`s
      from empty is a memory-safe BST; `findNode`/`contains`/`lookup` return
      the correct value.
- [ ] **G1b** Prove by composing: `insert` refinement (E) + `insert` preserves
      `IsBST`/`NoRedRed` (RBTree.v) + `findNode` refinement (FindSpec) +
      ref-count soundness (F).
- [ ] **G1c** (optional) Explicit black-height/balance theorem via `validAux`
      for a stated O(log n) height bound.
- [ ] **G1d** Discharge the module well-formedness side conditions
      (`source ⊧ σ`, `|-- denoteModule source`) for the concrete driver TU, so
      the top-level theorem is unconditional rather than parameterized. (These
      are standard BRiCk facts about a well-formed translation unit; today they
      are section hypotheses that nothing closes.)

## Phase H — Strengthen specs & tighten the C++ connection

Independent of the write-path; improves *what the connected specs actually say*.

- [ ] **H1** Strengthen `findNode_spec` (`FindSpec.v`): the found case currently
      asserts only `ret <> nullptr`. Extend the postcondition so that when
      `findNode k t = Some v`, the returned pointer satisfies
      `ret |-> _key |-> intR _ k ** _value |-> intR _ v` (borrowed, matching the
      `\prepost` fractional ownership) — i.e. the node actually holds the
      computed key/value. Reprove `findNode_ok`. This is what `Map::lookup`
      needs anyway.
  - [ ] H1a Decide the borrowed-ownership shape for the returned node
        (fraction/observation that composes back into `treeR q t`).
  - [ ] H1b Thread the value through the loop invariant (currently the
        invariant only tracks `findNode k t = findNode k tc`; add that a `Some`
        result pins the located node's fields).
  - [ ] H1c Reprove `findNode_ok`; update the README "what's connected" note.
- [ ] **H2** Add a `Print Assumptions` audit for each top-level `*_ok` theorem
      so the trusted base (the 2 BRiCk gaps, nothing more) is machine-visible
      and can't silently grow. Wire into a `make audit` target.

---

## Optional / stretch (not on the critical path)

- [ ] `Map::contains`, `Map::lookup`, `Map` constructor — thin wrappers over
      `findNode` once it composes.
- [ ] `Node::valid` runtime checker: prove it returns `>0` iff
      `IsBST ∧ NoRedRed ∧ uniform black-height`.
- [ ] `Iterator` (in-order traversal, heap-allocated parent chain) — large,
      separate effort.

## Explicitly out of scope

- **Delete.** The Daedalus C++ has no delete operation. The Lean `DoubleBlack`
  deletion model is a companion experiment, not needed for C++ verification.

---

## Cross-cutting cleanups

- [ ] `RefCount.v`: currently prose-only (0 definitions, pseudo-syntax specs).
      Either implement (D1b) or move the sketch to `docs/` and drop from the
      build until Phase 6.
- [ ] Add a `Print Assumptions` check (per key theorem) to CI/Makefile so the
      trusted base can't silently grow.
- [ ] Consider a `make audit` target: report admit/Admitted/Axiom counts per
      file so regressions are visible.
