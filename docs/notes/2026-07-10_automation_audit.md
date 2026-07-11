# Proof-automation audit + extraction plan (2026-07-10)

Audit of the tactic library (`WpTactics.v` generic / `Tactics.v` tree-specific /
`RebalanceDefs.v`) and the proof files (SetRebalanceLeft/Right, IsBlackSpec,
InsertSpec, InsSpec, FindSpec). Three parallel read-only surveys + a quantitative
invocation scan. Findings below are ranked by (payoff / effort / risk); each has a
concrete action. **Rule of engagement: validate every tactic change in a ~3s
faithful scratch, then rebuild only the affected file; never iterate against a
30-min proof file.**

Quantitative baseline (invocation counts across the 6 proof files):
`wp_operand_call_direct1` 33, `_null` 9, `treeR_node_fold` 25, `wp_read_field` 18,
`wp_read_local` 30, `wp_destroy_prim_temp` 37, `iExists (Vbool …)` 44,
`wp_unfold_node(*)` 27, `wp_srr_default` 7, `wp_srl_default` 2, `wp_guard_isblack*` 10.

## Headline finding
`SetRebalanceLeft.v` = 1002 lines, `SetRebalanceRight.v` = 624 lines. The gap is
NOT intrinsic — Right was written using the shared tactics (`wp_guard_isblack_true`,
`wp_srr_default`); Left still INLINES those same blocks verbatim (guard opener 5×,
default tail 5×, plus a hand-rolled ~52-line null is_red call in Case 2a). Migrating
Left onto the ALREADY-EXISTING tactics removes ~245 lines with ZERO new library code.

## Prioritized actions

### P0 — Migrate SetRebalanceLeft onto existing tactics (biggest win, no new lib code, low risk)
- Replace the 5 inlined `is_black(n)=true` guard openers with `wp_guard_isblack_true
  MODULE n_ptr`; the c=Red opener with `wp_guard_isblack_false MODULE n_ptr`.
- Replace the 5 inlined default tails with `wp_srl_default <c> <tree> n_ptr nl_ptr k v r rp rc`.
- Replace the hand-rolled Case-2a null is_red call (~52 lines) with
  `wp_operand_call_direct1_null` + the standard None-precond block (as Right:58 does).
- Expected: ~1002 → ~750 lines, faster compile, and Left/Right become true mirrors.
- Risk: low (tactics already proven on Right + on Left's other cases). One rebuild to confirm.

### P1 — Merge the twin guard tactics (D1: strongest library merge, no readability cost)
`wp_guard_isblack_true` / `wp_guard_isblack_false` (RebalanceDefs.v) differ only in
two correlated tokens: `(Some Black)`+`(Vbool true)` vs `(Some Red)`+`(Vbool false)`.
Collapse to `wp_guard_isblack modpf np col bval` (or one bool arg deriving both).

### P1 — Factor the call-precond+receive wrapper (attacks the 33× / 44× repetition)
Every `wp_operand_call_direct1(_null)` site is followed by the SAME ~15-line block:
`rewrite /is_*_spec /=; iExists _,(Vptr p); iSplit reflexivity; iSplitL "Hargp";
iExists p,(Some C|None),q; iSplit; iSplitL <resources>{...}` (precond) then `iIntros
(ret rx) "(Hany & Hres)"; wp_auto; wp_destroy_prim_temp; iModIntro; rewrite
operand_receive.unlock; iExists (Vbool b); iFrame; simpl; iDestruct post` (receive).
This "provide precond + receive Vbool result" wrapper is the single most-repeated
uncaptured shape (~22 preambles + ~19 receive-tails). Lift two tactics:
- `wp_call_isX_provide <c_opt> <resources-ipat>` — the precond provision;
- `wp_call_recv_bool <b>` — the receive-Vbool tail.
Then each guard/sub2 call collapses to: resolve + provide + recv. Biggest structural
dedup in the proof files (patterns 1–4 all embed these).

### P2 — Merge wp_operand_call_direct1 / _null (D3)
~40 of ~50 lines shared; only the `has_type (Vptr p)` discharge differs (structR vs
nullptr). Merge into one tactic taking the discharge as an `ltac:(...)` arg.

### P2 — Collapse wp_unfold_node / wp_unfold_node' / treeR_node_unfold (D2/O1)
3-way redundancy: both tactics reimplement inline what `treeR_node_unfold` proves,
and differ by one line (goal-wide vs `iEval … in H`). Make the tactics apply the
lemma; keep `wp_unfold_node'` as the primary (robust) one. Also: FindSpec:265's
`first [ rewrite treeR_node _at_as_Rep | rewrite _at_as_Rep ]` and FindSpec:344's
hand-inlined unfold should adopt these — but FindSpec needs the bound lp/rp/rc names
in Ltac scope, so provide a name-exposing variant.

### P2 — Move wp_field_to_primR to WpTactics.v (L1: layering fix)
It is fully generic (no tree specifics in the code) yet sits in Tactics.v.

### P3 — Qed-backed lemmas to shrink proof terms (compose with splitting; measure)
Big inlining tactics that expand a large term at each site — convert the CLOSED
sub-proofs to `Qed` lemmas:
- `wp_eval_ptr_neq_null` / `wp_eval_ptr_neq_nonnull` (close their goal, cleanest).
- `wp_eval_int_binop` (one lemma param'd by the eval lemma collapses 4 aliases).
- the `has_type_or_undef` discharge inside `wp_read_local` (30× — high leverage).
- the has_type/`nd_seqs` closed sub-proofs inside `wp_operand_call_direct1(_null)`.
Measure the compile-time effect on one file before doing all.

### P3 — Smaller lemma cleanups
- Derive `treeR_node_valid` from `treeR_node_nonnull` (O2: near-identical observers).
- De-duplicate `wp_step_debug` vs `wp_step` (D4: 16 branches kept in sync by hand).
- `is_red_ok` (IsBlackSpec) hand-inlines the operand call at :145 instead of using
  `wp_operand_call_direct1` — reconcile once the merged call tactic exists.

## Sequencing
Do **P0 first** (pure win, no lib change, shrinks the slow file, makes Left/Right
true mirrors → future rebalance edits half the cost). Then **P1** (guard merge +
call-wrapper tactics) since it removes the largest remaining repetition and every
future call site benefits. P2/P3 are lower-urgency polish; do P3 (Qed-ification)
only if per-file compile time still blocks Phase-D work.
