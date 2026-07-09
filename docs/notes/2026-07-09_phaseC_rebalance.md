# Phase C groundwork: setRebalanceLeft/Right_ok

*Created: 2026-07-09. Phase B (`is_black_ok`/`is_red_ok`) is done and `Qed` in
`coq/IsBlackSpec.v`; RebalanceSpec now `Require`s it for the real callee proofs.*

## Status entering Phase C
`coq/RebalanceSpec.v` has the full case-split scaffold (22 `admit`s) for
`setRebalanceLeft_ok` / `setRebalanceRight_ok`. The prologue works (args +
field-level `\pre` split into `Hrc/Hcolor/Hkey/Hval/Hleft/Hright/Hstruct`,
`Htree_r`, `Htree_nl`). The body is:
```
Sif (Eseqand (is_black(n), is_red(newLeft)))
    then <rotation: read newLeft->left as sub2, nested Sif on is_red(sub2), …>
    else <default: n->left = newLeft; return n>
```

## The unblocked increment: the `Eseqand` guard + default cases (C1b)
The default (no-rotation) cases need only Phase B (no `makeCopy`):
`c=Red`; `c=Black,newL=Leaf`; `c=Black,newL=Node Black …`;
`c=Black,newL=Node Red (non-Red-left) _ (non-Red-right)`.

Each evaluates the guard `is_black(n) && is_red(newLeft)` to `false`, then falls
through to the default path (`setRebalanceLeft c newL k v r = Node c newL k v r`,
proved by `setRebalanceLeft_default`).

### Guard evaluation — the new machinery needed
`Eseqand` short-circuits via `wp_operand_seqand` (expr.v:602): evaluate
`is_black(n)` under `wp_test`; if `false` short-circuit to `Vbool false`, else
evaluate `is_red(newLeft)`. Both operands are **calls to verified callees in
test position**. This is the SECOND occurrence of the direct-call pattern
(first: `is_red_ok` calling `is_black`), so per CLAUDE.md it justifies extracting
a reusable operand-context call resolver into the library (B1c).

Two wrinkles vs. `is_red_ok`'s single call:
1. **`wp_test` wrapper** around each call (from `Eseqand`), not a bare
   `wp_operand`. `rewrite /wp.WPE.wp_test /=` first (as in `is_black_ok`).
2. **Extra `Cnoop` cast** on the argument: `Ecast (Cnoop _) (Ecast Cl2r (Evar
   "n" …))`. Handle the `Cnoop` (const-qualification noop) before the arg read.
3. **Precondition assembly**: the callee `is_black_spec`'s `\prepost{c_opt}`
   wants `n_ptr |-> (_color |-> boolR q (color_to_bool c) ∗ structR)`, but here
   the fields are held SEPARATELY (`Hcolor`, `Hstruct`). Combine them (`iExists
   (Some c)`, frame `Hcolor`+`Hstruct` via `_at_sep`) — and get them back in the
   callee `\post` (read-only), then re-split for the remaining default-path
   field writes (`n->left = newLeft`). `is_red(newLeft)` similarly needs a
   `c_opt` derived from `newL` (Leaf → None with `nl_ptr=nullptr` from
   `treeR_leaf_implies_null`; `Node c_nl …` → `Some c_nl` from unfolding
   `Htree_nl`'s `treeR`).

## Captured guard goal (2026-07-09, Case 1 `c=Red`)
Context: `Hcolor : n_ptr |-> _color |-> boolR 1$m (color_to_bool Red)`,
`Hstruct`, the other fields, `Htree_r`, `Htree_nl : nl_ptr |-> treeR 1 newL`,
and `Hcont : ∀ x, x |-> treeR 1 (setRebalanceLeft Red newL k v r) -∗ ∀ x0, pn|->
anyR ∗ pnl|->anyR ∗ x0|->tptsto (Vptr x) -∗ Q x0`.
Goal:
```
wp source ρ (Sif None (Eseqand (Ecall is_black [Cnoop (Cl2r (Evar "n"))])
                                (Ecall is_red   [Cnoop (Cl2r (Evar "newLeft"))]))
                 (Sseq [Sdecl [Dvar "sub2" … newLeft->left …]; …])   (* rotation *)
                 <default>) K
```
For `c=Red`: `is_black(n)` returns `false` (color is Red) → `Eseqand`
short-circuits → `Vbool false` → `Sif` takes the else/default branch →
`n->left = newLeft; return n`; discharge via `setRebalanceLeft_default` +
`treeR_node_fold`.

## Rotation cases (C1c–C1e) — BLOCKED on Phase D
LL/LR rotations copy `sub2` via `makeCopy`, so they need the ref-count/COW model
(Phase D). Do the guard + all default cases first; leave rotations admitted.

## Guard mechanism — worked out step by step (2026-07-09, Case 1 c=Red)
These steps all build clean (verified individually against the AST); the ONLY
remaining snag is the `wp_nd_args` interaction (see caveat). Sequence for the
`Eseqand` guard's first operand `is_black((const Node*)n)`:
```coq
iApply (wp_if source); iNext.
rewrite /wp.WPE.wp_test /=.
iApply wp_operand_seqand.
rewrite /wp.WPE.wp_test /=.
(* --- evaluate is_black(n) as a direct call --- *)
iApply wp_operand_call;
  rewrite /wp_call /=; iIntros "%_"; rewrite /wp.WPE.Mbind /wp.WPE.Mmap /=.
iApply wp_operand_cfun2ptr_global; [ exact is_black_lookup | exact is_black_has_body | ].
iSplitL "HMOD"; [ iExact "HMOD" |].
iExists (_global is_black_name).
iSplit; [ iPureIntro; reflexivity |].
(* --- single arg (const Node*)n: strip Cnoop, read local, discharge has_type --- *)
wp_nd_args ltac:(iApply wp_operand_cast_noop;
                 wp_read_local "Hpn" (Vptr n_ptr);
                 iSplitR;
                 [ rewrite has_type_ptr';
                   iDestruct (observe (reference_to _ n_ptr) with "Hstruct") as "#_rt";
                   iDestruct (reference_to_elim with "_rt")
                     as "(%_align & %_nn & #_val & _)";
                   iSplitR; [ iApply "_val" |];
                   iPureIntro;
                   rewrite aligned_ptr_ty_erase_qualifiers /=; exact _align
                 | ]).
```
Key facts nailed down:
- The arg is `Ecast (Cnoop "const Node*") (Ecast Cl2r (Evar "n"))`. `wp_operand_cast_noop`
  (expr.v:716) leaves `has_type v ty ∗ Q v` — the extra obligation vs. a bare read.
- `has_type (Vptr n_ptr) (Tptr (const Node)) ⊣⊢ valid_ptr n_ptr ∗ [aligned_ptr_ty
  (const Node) n_ptr]` (`has_type_ptr'`, pred.v:193).
- Both discharged from `Hstruct` via `reference_to_elim` (pred.v:228): it yields
  `aligned_ptr_ty (Tnamed _Node_name) n_ptr` + `valid_ptr n_ptr`.
- `aligned_ptr_ty_erase_qualifiers` (ptrs.v:631) turns the goal's `const Node`
  alignment into plain `_Node = Tnamed _Node_name` alignment → `exact _align`.

### CAVEAT — the one thing still to fix (next session starts here)
`wp_nd_args` did NOT fully resolve the single-arg `nd_seqs` with the above eval
tactic: it left the trailing empty-list recursion goal `∀ pre post q, [ [wp_arg …]
= pre ++ q :: post ] -∗ Mbind …`, so the subsequent `wp_call_direct` failed with
"No matching clauses for match" (no `wp_fptr` in the goal yet). Root cause is
almost certainly that the eval tactic must leave EXACTLY ONE goal for
`wp_arg_prim`'s follow-through (`iIntros`), but our `iSplitR; [ discharge_has_type
| ]` leaves the read-continuation as the 2nd goal in a way that desyncs the
`repeat wp_nd_args_step` loop. Fix options to try:
1. Discharge the `has_type` INSIDE the operand continuation *before* it becomes a
   separate goal — i.e. restructure so `wp_operand_cast_noop`'s `has_type` is
   framed within the same bullet as the read (no `iSplitR` splitting the arg's
   continuation from the has_type).
2. Or hand-roll the 1-arg `nd_seqs` (it's a single element — unfold `nd_seqs`/
   `nd_seqs'` directly, `iIntros (pre post q) "%Heq"`, `destruct pre`, then the
   `Mret nil` base) instead of `wp_nd_args`, mirroring what `wp_nd_args_step` does
   but keeping the has_type discharge inline.
3. Compare with `is_red_ok` (IsBlackSpec.v): there the arg had NO `Cnoop`, so
   `wp_read_local` alone left exactly one goal and `wp_nd_args` closed cleanly.
   The `Cnoop`+has_type is the whole delta — encapsulate it as a
   `wp_arg_noop_read` helper that leaves one goal, then reuse for is_red(newLeft),
   is_red(sub2), and everywhere else Daedalus passes `(const T*)x`.
Once the arg resolves, the rest mirrors `is_red_ok`: `wp_call_direct … is_black_ok
is_black_func`; provide `is_black_spec` precond with ghost `Some Red` assembled
from `Hcolor`+`Hstruct` (`iExists _, (Vptr n_ptr); …; iExists n_ptr, (Some Red);
… iExists q; rewrite _at_sep; iFrame`); receive resources back; `is_black`
returns `false` (color=Red) so `Eseqand` short-circuits to `Vbool false` → `Sif`
else branch → default path via `setRebalanceLeft_default` + `treeR_node_fold`.

## Rules / anchors
- `wp_operand_seqand` expr.v:602; `wp_test` unfold as in `is_black_ok`.
- Direct call: `wp_operand_call` → `wp_operand_cfun2ptr_global` (INFER the callee
  name from the goal — do NOT pass the folded `is_black_name`, it blocks
  unification; that is why `wp_resolve_call` can't be used verbatim in operand
  context) → `wp_call_direct … is_black_ok is_black_func`. See `is_red_ok` in
  `coq/IsBlackSpec.v` for the exact working sequence.
- Default path fold: `setRebalanceLeft_default` (RebalanceSpec.v:80) +
  `treeR_node_fold` (Tactics.v).
- `treeR_leaf_implies_null`, `treeR_node_nonnull` for the `newL` case analysis.
