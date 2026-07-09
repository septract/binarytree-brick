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
