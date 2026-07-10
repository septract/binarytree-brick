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

### UPDATE 2026-07-09 (later): the nd_seqs snag is solved; the REAL blocker is the fun-type
Hand-stepping the single-arg `nd_seqs` (instead of `wp_nd_args`) works cleanly:
```coq
rewrite /wp.WPE.nd_seqs /=.
iIntros (pre post q) "%Hnd".
destruct pre as [| ?x0 [| ?x1 ?rest]]; simpl in Hnd; try congruence.
injection Hnd; clear Hnd; intros; subst; simpl.
rewrite /wp.WPE.Mbind /call.wp_arg /=.
iIntros (argp).
rewrite /wp_initialize /qual_norm /=. try rewrite wp_initialize_unqualified.unlock /=.
iApply wp_operand_cast_noop.
wp_read_local "Hpn" (Vptr n_ptr).
(* extract has_type facts persistently BEFORE iSplitR (Hstruct is spatial!) *)
iDestruct (observe (reference_to _ n_ptr) with "Hstruct") as "#_rt".
iDestruct (reference_to_elim with "_rt") as "(%_align & %_nn & #_val & _)".
iSplitR.
{ rewrite has_type_ptr'. iSplitR; [ iApply "_val" |].
  iPureIntro. rewrite aligned_ptr_ty_erase_qualifiers /=. exact _align. }
iIntros "?". rewrite /wp.WPE.Mmap /wp.WPE.Mret /=. iNext.
```
After this the goal is exactly
`wp_fptr (types (genv_tu σ)) (Tfunction (FunctionType "bool"
  [to_arg_type (Tptr (Tqualified (merge_tq QM (merge_tq QM QC)) "…Node"))]))
  (_global is_black_name) [argp] (λ v, …)`
and the `wp_fptr _ ?ft _ _ _` match DOES fire (verified via `idtac`).

**THE BLOCKER:** `wp_call_direct` then does
`change ft with (type_of_value (Ofunction is_black_func))` and that fails with
"No matching clauses for match". Reason: the call-site `ft` above has the arg
type `to_arg_type (Tptr (Tqualified (merge_tq QM (merge_tq QM QC)) "…Node"))`
— extra `merge_tq QM` qualifiers coming from the `Cnoop`/`(const T*)` cast at
the call site — whereas `type_of_value (Ofunction is_black_func)` has the
*declared* arg type `Tptr (Qconst _Node)`. They are NOT convertible, so `change`
(and hence `wp_call_direct`) fails. In `is_red_ok` the call site's arg had no
such extra qualification, so `change` succeeded.

Fix directions for next session (pick one, verify with the 3-second scratch idea
won't work here since it needs the AST — budget one AST build):
1. Find/build a `wp_fptr`-level lemma that tolerates convertible-up-to-
   qualifier-normalization function types, or normalize the goal's `ft` first
   (e.g. `rewrite` a `to_arg_type`/`merge_tq QM` simplification: `merge_tq QM q =
   q`, and `to_arg_type` of a qualified ptr = the erased/normalized ptr). Look
   for `merge_tq_QM_l`/`merge_tq_id`/`to_arg_type` lemmas in
   `.brick-workspace/.../specs/*.v` and `syntax/types.v`.
2. Or apply `wp_fptr_of_func_ok` DIRECTLY (skip the `change`): `iApply
   (wp_fptr_of_func_ok …)` and let unification/`f_equal` reconcile the fun types,
   discharging the qualifier mismatch with a `types_compat`/`type_of_value`
   rewrite. Check `wp_fptr_of_func_ok`'s statement — it may already quantify the
   function type and only need the arg *values* to line up.
3. Or prove a small `func_ok`-conversion: `is_black_ok` at the call-site's
   qualified function type from `is_black_ok` at the declared type (they should
   be equal after `merge_tq QM`/`to_arg_type` normalization).
This qualifier-normalization is the ONLY thing between here and closing the
`c=Red` default case; everything up to and including the `wp_fptr` goal is
proved. Once the call resolves, provide `is_black_spec` precond (ghost `Some
Red` from `Hcolor`+`Hstruct`), get `false` back, short-circuit `Eseqand`, take
the `Sif` else branch, close via `setRebalanceLeft_default` + `treeR_node_fold`.

### RESOLVED 2026-07-09: Case 1 (c=Red) of setRebalanceLeft_ok is CLOSED
The fraction mismatch was fixed by parameterizing `is_black_spec`/`is_red_spec`
by the fraction: `\prepost{c_opt q} match c_opt with Some c => n_ptr |-> (_color
|-> boolR q … ∗ structR q) | None => [|…|] end` (note: `\prepost{c_opt q}` — one
brace, space-separated, types inferred; `{c_opt:..}{q:..}` double-brace does NOT
parse). `is_black_ok`/`is_red_ok` re-proved unchanged except the prologue now
binds `q` from the spec (`iDestruct "Hspec" as (n_ptr c_opt q) …`) and the Some
case drops the inner `iExists q`. Both still `Qed`. With `q` caller-chosen, the
RebalanceSpec caller lends `cQp.m 1` and gets it back concretely, so
`treeR_node_fold` folds. Case 1 is fully proved (RebalanceSpec: 22→21 admits);
the final field write used `wp_field_to_primR "Hleft_new" "Hleft2" (Vptr nl_ptr)
I` (tptstoR→ptrR) before the fold, and the return needed `repeat wp_step` to
strip the fupd/`KP`/`ReturnVal` down to `Q retp`. The full working sequence
below is now committed as the Case-1 proof; the remaining default cases
(2a Leaf, 2b Node Black, 2b-Red non-rotating) reuse it verbatim.

### (historical) guard+default path mapping — fraction mismatch (now fixed above)
The full `c=Red` default case was driven end-to-end and every step builds; the
ONLY remaining error is a fraction mismatch at the final `treeR_node_fold`.
Working sequence (all verified against the AST, in order):
1. `wp_if`/`wp_test`/`wp_operand_seqand` — enter guard.
2. `is_black(n)` call: `wp_operand_call` → hand-stepped 1-arg `nd_seqs`
   (`iIntros (pre post q) "%Hnd"; destruct pre; injection; subst`) →
   `wp_operand_cast_noop` + `wp_read_local "Hpn"` + has_type discharge from
   `Hstruct` via `reference_to_elim` + `aligned_ptr_ty_erase_qualifiers`.
3. **fun-type qualifier fix (KEY):** the call-site `ft` (with `to_arg_type`/
   `merge_tq QM (merge_tq QM QC)`) is reconciled with
   `type_of_value (Ofunction is_black_func)` by
   `match goal with |- context[wp_fptr _ ?ft _ _ _] => replace ft with
   (type_of_value (Ofunction is_black_func)) by (vm_compute; reflexivity) end`
   — `vm_compute` (NOT `change`) because they're equal only after
   normalization. Then `iApply (wp_fptr_of_func_ok_compat _ _ _ _ _ _ tu_compat)`
   (the `_compat` variant, since the goal uses `(genv_tu σ).(types)` not
   `source.(types)`), framing `code_at_of_denoteModule` and
   `(is_black_ok MODULE)` — note `is_black_ok` needs `MODULE` applied explicitly.
4. Provide `is_black_spec` precond: `iExists argp (Vptr n_ptr); …; iExists n_ptr
   (Some Red); …; iExists (cQp.m 1); rewrite _at_sep /=; iFrame "Hcolor Hstruct"`.
   (The arg temp must be named — `iIntros "Hargp"`, not `"?"` — to frame the
   outer `pv|->tptsto`.)
5. Post-call: `iIntros (ret) "Hpost"; iIntros (rx) "(Hany & Hres)"; wp_auto;
   wp_destroy_prim_temp "Hany"; iModIntro; rewrite operand_receive.unlock /=;
   iExists (Vbool false); iFrame "Hres"`. `is_black` of a Red node = `false`.
6. `simpl` reduces `is_true (Vbool false) = Some false` → `Eseqand`
   short-circuits (NO is_red call) → default path.
7. Default: `iIntros (addr); wp_read_local "Hpn"` (`res=n`); `wp_assign_setup;
   wp_read_local "Hpnl"; wp_offset "Hleft"; wp_assign_member_field "Hres_local"
   (Vptr n_ptr) "Hstruct" "Hleft"` (`res->left=newLeft`); read `res`, destroy
   local; `wp_revert_offset "Hleft_new"`.

**THE ONE REMAINING BLOCKER (fraction mismatch):** `is_black_spec`'s
`\prepost{c_opt}` has `Some c => Exists (q : Qp), n_ptr |-> (_color |-> boolR q …
∗ structR q)`. The `Exists q` is INSIDE the prepost resource, so on return the
borrowed color+struct come back at an OPAQUE `q_c` (even though we lent
`cQp.m 1`), while the other node fields (`Hrc/Hkey/Hval/Hleft/Hright`) are still
`cQp.m 1`. `treeR_node_fold` needs ALL fields at the SAME fraction, so it can't
fold (`iFrame` fails on `n_ptr |-> _color |-> boolR q_c$m true`).

**RECOMMENDED FIX (do this first next session):** parameterize `is_black_spec`
(and `is_red_spec`) by the fraction as a spec-level `\with{q}` (or make it a
`\prepost` argument) instead of an internal `Exists q`:
```
\arg{n_ptr} "n" (Vptr n_ptr)
\prepost{c_opt : option Color}{q : Qp}   (* q now caller-chosen, returned concretely *)
  match c_opt with Some c => n_ptr |-> (_color |-> boolR q (color_to_bool c) ∗
                                        structR _Node_name q)
                 | None => [| n_ptr = nullptr |] end
```
Then the caller passes `q := cQp.m 1` and gets it back at `cQp.m 1` (no opaque
existential), so `treeR_node_fold` folds. `is_black_ok`/`is_red_ok` already
handle an arbitrary `q` (they `iDestruct "Hpre" as (q) "..."`), so re-proving
them under the new spec is essentially a no-op — just move the `q` binder from
inside the resource to the spec's `\with`/`\prepost` binder and re-run the two
`Qed`s (~1 min each) + this RebalanceSpec proof. Alternative (worse): lend
`is_black` a fractional half and recombine — but `treeR_node_fold` wants full
`cQp.m 1`, so fraction-splitting adds bookkeeping for no benefit.

Everything else in the `c=Red` default case is proven. Once the fraction is
concrete, the fold + `iApply ("Hcont" $! n_ptr with "Htree")` + frame
`Hpn`/`Hpnl`→anyR + `Hret_store` closes it. The other default cases
(`newL=Leaf`, `newL=Node Black`, `newL=Node Red non-Red/non-Red`) reuse the same
guard machinery (is_black returns true then is_red returns false → still
short-circuits to default) and the same default-path tail.

### (superseded) earlier caveat about wp_nd_args leaving two goals
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

## PROGRESS 2026-07-09 (session 2): 3 default cases proved + 2 reusable tactics

Proved (all `Qed`-clean, committed):
- **Case 1** `c=Red` — commit `2f05b3c`.
- **Case 2a** `c=Black, newL=Leaf` — commit (Case 2a): is_black=true then
  is_red(newLeft=null)=false. First null-argument is_red.
- **Case 2b-Black** `c=Black, newL=Node Black …` — is_red(newLeft)=false via the
  `Some Black` precond (borrows newL's `_color+structR` after `wp_unfold_node`).

Extracted into `WpTactics.v` (both generic, re-entrant — validated by two uses
in one proof):
- **`wp_operand_call_direct1 HMOD lookup body fname fok func_def H_local vp H_struct`**
  — resolve `f((const T*) local)` in operand/test position → callee `fs_spec`
  precondition. Discharges the `Cnoop` `has_type` from `H_struct`'s `structR`.
- **`wp_operand_call_direct1_null HMOD lookup body fname fok func_def H_local H_align`**
  — same but the argument is `nullptr` (e.g. `is_red(sub2)` with `sub2=null`):
  `has_type` from `valid_ptr_nullptr` + `align_of` witnessed by any live
  `structR` (`H_align`).
Both `iClear` their persistent intermediates + clear the pure `aligned_ptr_ty`/
`<>nullptr` facts so a proof can call them multiple times without name clashes;
the tu-models premise is dropped with an anonymous `iIntros "%"`.

### Case 2b-Red default sub-cases — status
`newL = Node Red …` with neither child Red enters the rotation BODY (guard
`true && true`), then reads `sub2 = newLeft->left`, `is_red(sub2)` (LL-check),
`sub2 = newLeft->right`, `is_red(sub2)` (LR-check); both false ⇒ fall to the
trailing default. The **both-children-Leaf** sub-case is fully worked out and
builds through both rotation-check short-circuits (using
`wp_operand_call_direct1_null` for the two null `is_red(sub2)` calls, and
`wp_lval_assign`+`wp_assign_local` for the `sub2 = newLeft->right` reassignment)
— the ONLY open step is the final re-fold of `newL = Node Red Leaf k_nl v_nl
Leaf`: its Leaf children are stored reduced (`nullptr |-> as_Rep …`) and don't
syntactically frame against `treeR_node_fold`'s `treeR q Leaf` child slots (the
CLAUDE.md `treeR` fixpoint gotcha). Fix next session via the faithful-scratch
loop to get the child form to match (likely `rewrite -treeR_leaf` on the slot,
or fold with the children provided as `treeR q Leaf` before reduction). The full
proof body is preserved in git history (this commit's parent WIP) / reconstruct
from the pattern above. The other 2b-Red default sub-cases (`newL->left=Node
Black`, `newL->right=Node Black`, etc.) mirror it with a non-null `is_red(sub2)`
(Some Black) instead of the null one. Rotation (LL/LR) cases remain blocked on
Phase D (`makeCopy`).

## PROGRESS 2026-07-09 (session 2, cont.): 2b-Red both-Leaf CLOSED — treeR fold gotcha solved

The both-children-Leaf 2b-Red case is now fully proved (RebalanceSpec 19→18
admits). The `treeR` fixpoint-reduction fold gotcha is SOLVED (found via a
3-second faithful scratch, `ScratchFold.v`, since deleted):

**Folding `Node c` with reduced (`as_Rep`) `Leaf` children** — `iFrame` fails
(the `1$m` = `cQp.m 1` hyp form differs from the fold's `q` via the non-identity
coercion path `cQp.frac; cQp._mut`; see the build warning), but `iExact` matches
up-to-definitional. Working pattern:
```coq
iApply (treeR_node_fold (cQp.m 1) c l k v r lp rp rc p).
iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].   (* left Leaf child  *)
iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].   (* right Leaf child *)
rewrite !_at_sep.                                    (* split p|->(f1∗f2∗…) *)
iSplitL "Hf1"; [ iExact "Hf1" |]. … ; iExact "Hlast" (* fields via iExact  *)
```
When a child is a live non-Leaf `treeR` hyp (e.g. the outer fold in 2b cases),
`iFrame`/`$` works normally — the issue is specific to freshly-materialised Leaf
children.

Also learned: **`sub2` (the rotation-body local) is destroyed at the END of the
rotation-body `Sseq`**, before the outer default sequence — so `wp_destroy_local
"Hsub2_local"` must come right after the LR-check short-circuit, NOT interleaved
with the outer `res` handling.

### Remaining default sub-cases (all mechanical, same patterns)
- `newL=Node Red, left=Leaf, right=Node Black` (RebalanceSpec ~L578): LL null →
  false; LR `is_red(sub2=right=Node Black)` → false via Some-Black (unfold the
  right child `_ntr` to borrow its color/struct).
- `newL=Node Red, left=Node Black, right=Leaf` (~L585): LL Some-Black false; LR
  null false.
- `newL=Node Red, left=Node Black, right=Node Black` (~L590): both Some-Black.
Each combines: guard true/true, sub2 read/reassign, one null + one Some-Black
`is_red(sub2)` (or two Some-Black), unfold the relevant child to borrow its
color/struct, then default-path fold (outer `Node Black newL k v r`; inner newL
re-fold with the appropriate child forms). The LL/LR ROTATION cases (~L576/581/
587) remain blocked on Phase D (`makeCopy`). `setRebalanceRight_ok` (~L713+) is
the full mirror.

## PROGRESS 2026-07-09 (session 2, final): 6 default cases proved (RebalanceSpec 22→16)

setRebalanceLeft_ok default cases all proved except one:
- c=Red ✓; c=Black,newL=Leaf ✓; c=Black,newL=Node Black ✓;
- 2b-Red both-children-Leaf ✓;
- 2b-Red left=Leaf,right=Node Black ✓ (Some-Black is_red on unfolded right child);
- 2b-Red left=Node Black,right=Leaf ✓ (mirror);
- **2b-Red left=Node Black,right=Node Black — NOT done** (only remaining default).

### The double-Node-Black case's open issue
The full ~195-line proof was written (both children Node Black ⇒ both LL and LR
checks are Some-Black is_red(sub2) on unfolded children). It builds through the
guard + is_red(newLeft) but fails at `wp_unfold_node "_ntl"` (unfolding the LEFT
child, which is `_lp |-> treeR (Node Black l_ll k_ll v_ll r_ll)`):
`iExistDestruct: cannot destruct (_lp |-> as_Rep …)`. Because the child's
[Node Black …] is a concrete constructor, its `treeR` is eagerly reduced to
`as_Rep g`, and `wp_unfold_node`'s `rewrite _at_as_Rep` apparently doesn't fire
on that already-reduced form (the CLAUDE.md `treeR` gotcha, but for the UNFOLD
direction rather than the fold). In 2a/2b-Black/the two mixed cases, only ONE
child needed unfolding and it worked because... [investigate: those unfolded the
child via the tactic too — the difference may be that here `_ntl` was produced by
the OUTER `wp_unfold_node "Htree_nl"` in already-`treeR`-applied form]. Fix
direction (needs a faithful scratch, ~3s, NOT the ~20-min full build which this
case pushed RebalanceSpec to): make a `wp_unfold_node_concrete` variant that does
`iRevert H; rewrite treeR_node _at_as_Rep; iIntros H; iDestruct …` (explicit
`treeR_node` first) for children with concrete-constructor trees. Then the
double-Black case = the two mixed cases combined (left child re-folded right after
its LL-check to free `_n*` for the right child's unfold, as already written in the
reverted WIP).

**Build-time warning:** RebalanceSpec.v full recheck is now ~18-20 min (6 large
Iris proofs, whole-file recheck by coqc). Iterate new cases via a faithful
scratch (RBTree/TreeRep/Tactics only, ~3s) per CLAUDE.md, NOT the full build.
Remaining: the double-Black default case, all LL/LR ROTATIONS (blocked on Phase D
makeCopy), and the entire `setRebalanceRight_ok` mirror.

## DEBUG 2026-07-09 (session 3): root-caused + fixed the nested-unfold gotcha

**Bug:** `wp_unfold_node H` does `iRevert H; rewrite _at_as_Rep; iIntros H`.
`_at_as_Rep : p |-> as_Rep f ⊣⊢ f p` is applied by a GOAL-WIDE `rewrite` with no
occurrence control. When the reverted `H : _lp |-> as_Rep …` sits in a goal that
ALSO contains other `as_Rep` terms — e.g. a sibling child's already-reduced
`treeR (Node …)`, or the folded left child `Htree_l_child` — `rewrite` fires on
the FIRST `as_Rep`, which may not be `H`. Then `H` stays `_lp |-> as_Rep …` and
the following `iDestruct H as (lp rp rc) "(...)"` throws `iExistDestruct: cannot
destruct`. The single-child cases (2a/2b-Black/the two mixed) worked only because
no competing `as_Rep` was present; the double-Node-Black case has two.

**Verified** in a ~5s faithful scratch (`ScratchUnfold.v`, since deleted): with a
competing `treeR (Node Red …)` in scope, the old `iRevert; rewrite _at_as_Rep;
iIntros; iDestruct as (…)` FAILS (confirmed with a `Fail` guard), while
`iDestruct (treeR_node_unfold with "H") as (lp rp rc) "(...)"` succeeds — because
it targets only the named hypothesis, no goal-wide rewrite.

**Fix (committed):**
- `treeR_node_unfold` (Tactics.v) — the entailment `p |-> treeR q (Node c l k v
  r) |-- ∃ lp rp rc, lp|->treeR l ∗ rp|->treeR r ∗ p|->(fields)`; reverse of
  `treeR_node_fold`.
- `wp_unfold_node' H` (Tactics.v) — robust variant using
  `iDestruct (treeR_node_unfold with H) as (…) "(...)"`. Use it for CHILD
  unfolds / any unfold where a competing `as_Rep` may be in scope;
  `wp_unfold_node` remains fine when `H` is the only `treeR (Node …)`.

**General lesson:** never `rewrite _at_as_Rep` (or any `treeR`/`as_Rep`
equational lemma) goal-wide when more than one `as_Rep` can be present — apply
the entailment to the specific hypothesis with `iDestruct (… with "H")` instead.
This is the occurrence-control analogue of the CLAUDE.md "treeR is a Fixpoint"
gotcha. If other multi-node proofs (InsSpec, makeCopy) hit the same wall, reach
for `wp_unfold_node'`.

## RESOLVED 2026-07-10: double-Node-Black CLOSED — all setRebalanceLeft defaults done

The careful-debugging strategy worked end to end. The nested-unfold wall had TWO
layers, both fixed in `wp_unfold_node'`:
1. **Occurrence ambiguity** — goal-wide `rewrite _at_as_Rep` fires on the wrong
   `as_Rep` when a competing one (sibling child) is in scope.
2. **Full reduction** — a fully-concrete child tree `treeR (Node Red (Node
   Black..) .. (Node Black..))` reduces eagerly to nested `as_Rep`, so any lemma
   with a `treeR (Node …)`-headed LHS (`treeR_node`, `treeR_node_unfold`) no
   longer matches and can't be refolded by unification.

Both are killed by `iEval (rewrite _at_as_Rep) in H`: it targets only `H` (no
occurrence ambiguity) and rewrites `H`'s CURRENT (reduced) form (no `treeR`-head
requirement). Plus, a per-case detail: before unfolding one child, `iRename` the
sibling's still-live child treeR out of the `_ntr` slot so the child unfold's
fresh `_ntl/_ntr/_n*` don't clash.

`setRebalanceLeft_ok`: all 7 DEFAULT (no-rotation) cases proved (RebalanceSpec
22→15 admits). Remaining: LL/LR ROTATIONS (blocked on Phase D makeCopy) and the
entire `setRebalanceRight_ok` mirror (which will reuse every tactic/pattern here
verbatim, left/right swapped).

## PROGRESS 2026-07-10 (session 4): refactor + setRebalanceRight started

Per the "refactor before mirroring" plan, extracted the verbatim-repeated blocks
into reusable tactics (all validated by rebuild, RebalanceSpec 15→13 admits):
- `wp_guard_isblack_true np` / `wp_guard_isblack_false np` (RebalanceSpec.v — they
  name source/is_black_ok/MODULE): the c=Black / c=Red guard openers (enter
  Sif/Eseqand, eval is_black(n) to true/false, recover node _color/_struct).
- `wp_srl_default c newLtree np nlp k v r rp rc` / `wp_srr_default c newRtree np
  nrp k v l lp rc` (Tactics.v): the default no-rotation tail (res=n; res->X=newX;
  return res; fold Node c … ; discharge Hcont), left / right mirror.
  Ltac note: pass proof-local Coq vars as args (tactic bodies can't reference
  them free), and bind introduced names (addr/retp/ret/rx) with `let _ := fresh`.

setRebalanceLeft_ok c=Red & 2b-Black refactored to use them; setRebalanceRight_ok
c=Red and newR=Node-Black proved via the mirror tactics.

### setRebalanceRight AST body (map_int_int_cpp.v:93926) — confirmed
NOT a blind left/right swap; read it carefully:
```
Sif (Eseqand (is_black n) (is_red newRight))
  then Sseq [ sub2 = newRight->left;   Sif (is_red sub2) [RL rotation; return] Sskip;
              sub2 = newRight->right;  Sif (is_red sub2) [RR rotation; return] Sskip ]
  else Sskip;
  res = n; res->right = newRight; return res
```
KEY: the sub2 read order is **left then right** — SAME as setRebalanceLeft. So
the DEFAULT (no-rotation) sub-cases ARE close mirrors of the setRebalanceLeft
ones: identical sub2 field-read order, `is_red(sub2)` checks; only the tail
(`res->right=newRight`, fold `Node c l k v newRtree`) differs — handled by
`wp_srr_default`. Remaining setRebalanceRight default cases to do (mirrors of the
named setRebalanceLeft cases, swap Htree_nl→Htree_nr, nl_ptr→nr_ptr, Hpnl→Hpnr,
wp_srl_default→wp_srr_default, and the newR subtree in the folds):
- newR=Leaf  (mirror of 2a);
- newR=Node Red, both grandchildren Leaf/Black combinations (mirror of the four
  2b-Red default sub-cases — the sub2=left is the RL check, sub2=right the RR).
RR/RL ROTATION cases stay blocked on Phase D (makeCopy). RebalanceSpec: 13 admits
(9 rotations across both fns + a few) remain.

## COMPLETE 2026-07-10 (session 4 end): all rebalance DEFAULT cases proved

Answer to "do we need to finish the mirror?": strictly `setRebalanceRight_ok`
stays `Admitted` regardless (its RR/RL rotations need Phase D), but leaving the
mirror half-done was an asymmetric, stale state — so we finished all its DEFAULT
cases. Both `setRebalanceLeft_ok` and `setRebalanceRight_ok` now have ALL 7
default (no-rotation) cases proved. RebalanceSpec: 22 → 8 admits, and the 8 that
remain are EXACTLY the LL/LR/RL/RR rotation cases (4 per function... actually the
non-rotating structure leaves the true rotation branches), all blocked on Phase D
(makeCopy + ref-count/COW).

The refactor paid off: with wp_guard_isblack_true/false, wp_srl_default/
wp_srr_default, wp_operand_call_direct1(_null), and wp_unfold_node', each default
case is now the guard opener + the case-specific is_red(sub2) checks + a
one-line tail. The setRebalanceRight defaults mirror the setRebalanceLeft ones
directly (sub2 read order left-then-right in both).

**Build-time caveat (important for the next session):** RebalanceSpec.v is now
~1700 lines of dense Iris and a full `coqc` recheck takes ~70 min. Do NOT iterate
new cases against it — use a ~3s faithful scratch (RBTree/TreeRep/Tactics only)
to nail any tactic first. If more rebalance work is needed, consider splitting
the file. NEXT real frontier: Phase D (makeCopy/RefCount) — the sole gate for the
rotation cases here AND for ins_ok.
