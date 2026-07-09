# Phase B groundwork: is_black_ok / is_red_ok

*Created: 2026-07-08. Prep notes so the next push starts fast (per CLAUDE.md,
avoid guessing against ~15-20 min AST builds).*

## Status entering Phase B
Both BRiCk framework gaps are closed (Gap 1 = sound `align_of_function` axiom,
proved `wp_operand_cfun2ptr_global`; Gap 2 = `black`/`red` inlined to literals in
`map.h`). `insert_ok`, `findNode_ok` build clean. Trusted base = one axiom.
`is_black_ok`/`is_red_ok` are the smallest remaining write-path callee
obligations (admitted specs in `InsertDefs.v`) and are now unblocked.

## The C++ under proof (from the regenerated AST, `map_int_int_cpp.v:93516`)

`is_black` (`Dmethod n12491`), body:
```
Sreturn_val
  (Eseqor
    (Ebinop Beq (Ecast Cl2r (Evar "n"))                       -- n == nullptr
                (Ecast (Cnull2ptr t6089) Enull) Tbool)
    (Ebinop Beq
      (Ecast (Cintegral Tint) (Ecast Cl2r
         (Emember true (Ecast Cl2r (Evar "n"))
                  (Field (field_name.Id "color") false Tbool))))   -- (int)n->color
      (Ecast (Cintegral Tint) (Ebool false)) Tbool))               -- == (int)false
```
i.e. `return (n == nullptr) || ((int)n->color == (int)false);`
Note: the bool comparison is promoted to `int` (two `Cintegral Tint` casts).

`is_red` (`Dmethod n12492`, `map_int_int_cpp.v:93532`):
```
Sreturn_val (Eunop Unot (Ecall <is_black>(n)))
```
i.e. `return !is_black(n);` — one call (uses the now-proved direct-call
machinery / `wp_resolve_call`) + boolean negation.

## Spec (already stated, `InsertDefs.v:307`)
`is_black_spec`: `\arg n_ptr` + `\prepost{c_opt : option Color}` where None ⇒
`n_ptr = nullptr`, Some c ⇒ `n_ptr |-> (_color |-> boolR q (color_to_bool c) **
structR _Node_name q)`; `\post` returns `Vbool (None→true | Black→true |
Red→false)`. `is_red_spec` is the negation. Read-only (`\prepost`).

## New wp patterns needed (not yet exercised in this repo)
1. **`Eseqor`** (short-circuit `||`): find BRiCk's `wp_operand`/`wp_test` rule
   for `Eseqor` — likely evaluates LHS to a bool, then short-circuits or
   evaluates RHS. Case-split on `c_opt` (None: LHS `n==nullptr` is true, whole
   thing true; Some: LHS false, RHS decides).
2. **`Ebinop Beq` on pointers** (`n == nullptr`): the null case uses
   `Cnull2ptr`; the non-null (Some) case needs `n_ptr <> nullptr` (from
   `structR`'s `nonnullR`, like `treeR_node_nonnull`).
3. **`Cintegral Tint` on a bool** + **`Ebinop Beq` on the promoted ints**: the
   `color == false` compare promotes both to int. Need the eval rule for
   `Cintegral` from a bool value and integer `Beq`.
4. **field read of `_color`** as `boolR` (have `wp_read_field`-style tactics in
   FindSpec/Tactics to borrow from).

## Suggested method (fast loop)
- One instrumented build of a scratch `is_black_ok` (dump the goal after
  `wp_func_intro` + arg extraction + `Sreturn_val`) to see the exact `Eseqor`
  goal shape. Then reproduce in a faithful AST-free-ish scratch if possible, or
  iterate the `Eseqor`/`Cintegral` handling directly.
- `is_red_ok` should be quick once `is_black_ok` is done + the direct-call
  machinery (already proved) resolves the `is_black(n)` call; then `Eunop Unot`.

## Grep anchors
- BRiCk `Eseqor` rule: `grep -rn 'Eseqor' .brick-workspace/fmdeps/BRiCk/rocq-skylabs-brick/theories/lang/cpp/logic/`
- `Cintegral` / bool→int: `grep -rn 'Cintegral\|wp_operand_cast_integral' …/logic/expr.v`

## Exact BRiCk rules found (pinned tree)
- `wp_operand_seqor` (expr.v:613): `wp_test e1 (fun c _ => if c then Q (Vbool c)
  else wp_test e2 (fun c _ => Q (Vbool c) …)) |-- wp_operand (Eseqor e1 e2) Q`.
  So: evaluate LHS to bool `c`; if true, done with `Vbool true`; else evaluate
  RHS. Maps onto the `c_opt` case split (None→LHS true; Some→LHS false→RHS).
- `wp_operand_cast_integral` (expr.v:787): `wp_operand e (fun v _ => ∃ v',
  [| conv_int tu (type_of e) t v v' |] ** Q v' …) |-- wp_operand (Ecast
  (Cintegral t) e) Q`. Need `conv_int` for bool→int (false→0, true→1).
- Null compare uses `Ecast (Cnull2ptr _) Enull`; pointer `Ebinop Beq`.
- Still need: `wp_test` unfolding rule, integer `Ebinop Beq` eval rule
  (grep `eval_binop`/`Beq` in semantics/operator.v), `conv_int` lemmas for bool.

## Recommended first step next session
Write `coq/InsSpecB.v` (or add to a scratch) proving `is_black_ok` against
`InsertDefs`. Instrument with `idtac` after `wp_func_intro` + arg-extract +
stepping `Sreturn_val`, ONE build to capture the `Eseqor` goal, then iterate.
Budget several AST builds; do NOT guess.
