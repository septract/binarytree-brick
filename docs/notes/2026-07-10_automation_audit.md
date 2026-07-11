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

## Sequencing (ORIGINAL — dedup-driven; superseded by the re-sequencing below)
Do **P0 first** (pure win, no lib change, shrinks the slow file, makes Left/Right
true mirrors → future rebalance edits half the cost). Then **P1** (guard merge +
call-wrapper tactics) since it removes the largest remaining repetition and every
future call site benefits. P2/P3 are lower-urgency polish; do P3 (Qed-ification)
only if per-file compile time still blocks Phase-D work.

## RE-SEQUENCING (2026-07-10): goal is a GENERALLY-REUSABLE tactic library
Motivation clarified: the point is to push ONE demo application (this RB-tree) all
the way through and *see where we land on reusability* of the GENERIC layer
(`WpTactics.v` — usable on any C++/BRiCk code). So rank by GENERALITY, not just
by dedup within this repo. Two consequences:

- The old **P0** (migrate SetRebalanceLeft) produces ZERO generic assets — it is
  tree-specific cleanup. Still worth doing, but as a **dogfooding stress-test** of
  the generic tactics, not the headline.
- New audit dimension — **hidden hardcoded assumptions**: a tactic may only work
  because these proofs follow naming conventions (literal Iris hyp names like
  `"HMOD"`, `"Hpn"`, `"Hcont"`, `"Hargp"`, `"Hstruct"`, or an assumed spec shape).
  That is fine for the tree-specific layer, but **anything promoted to the generic
  layer must take hyp names as parameters or use goal-matching — never assume
  them.** Every generic-layer item below must be checked against this.

Caveat: this repo is currently the ONLY consumer, so "generally usable" is
aspirational — the proxies are (a) strict no-hardcoded-assumptions discipline in
`WpTactics.v`, and (b) dogfooding via the tree proofs. Keep the tree migration in
the loop precisely as that stress-test.

Execution order (generic-library first):

**G1 — `wp_open_func` (generic flagship).** The `func_ok` prologue is byte-identical
across all 5 `*_ok` proofs and reusable on ANY BRiCk `func_ok` goal. Add
`wp_open_func <func_def>` to WpTactics.v (Layer 2/3): does `rewrite /func_ok; iSplit;
[iPureIntro; reflexivity |]; iIntros "!>" (Q vals) "Hspec"; iApply wp_func_intro;
rewrite /<f>_func /=` and stops before the per-proof spec destructs. Must NOT bake in
`iPoseProof MODULE as "#HMOD"` (FindSpec has no MODULE) — either omit it (caller adds
`HMOD` when needed) or provide a `wp_open_func_mod modpf f` variant. Dogfood: drive
all 5 prologues (InsSpec adds `iLöb` before it). Refs: InsSpec.v:105, InsertSpec.v:63,
IsBlackSpec.v:18/:127, FindSpec.v:365.

**G2 — consolidate + de-hardcode the generic call machinery.** (a) Lift the shared
callee-resolution PREFIX (`iApply wp_operand_call; …; iApply wp_operand_cfun2ptr_global;
iSplitL HMOD; iExists (_global fname); iSplit`) duplicated in `wp_resolve_call`,
`wp_operand_call_direct1`, `_null`, and inline in IsBlackSpec:145 → one
`wp_resolve_callee HMOD lookup body fname`. (b) Merge `wp_operand_call_direct1`/`_null`
(≈40/50 lines shared; differ only in the has_type discharge) via an `ltac:(...)`
discharge arg. (c) Take `HMOD`/`Hargp` as PARAMETERS (currently hardcoded) so the
tactics are reusable outside these proofs. Dogfood: reconcile IsBlackSpec `is_red_ok`
(:145) onto the merged tactic.

**G3 — generic-layer hygiene / layering.** Move `wp_field_to_primR` into WpTactics.v
(L1 — it is generic but sits in Tactics.v). Fix tree-leaking DOCSTRINGS in WpTactics.v
(`tptstoR_to_primR`, `wp_eval_ptr_neq_*`) so the generic file reads as generic.
De-duplicate `wp_step_debug` vs `wp_step` (16 branches hand-synced). A clean,
correctly-layered `WpTactics.v` IS the reusable product.

**G4 — Qed-backed generic closers (perf + library quality).** Convert closed-goal
tactics to Qed lemmas: `wp_eval_ptr_neq_null/nonnull`, `wp_eval_int_binop` (one lemma
param'd by the eval lemma collapses the 4 aliases), the `has_type_or_undef` discharge
inside `wp_read_local` (30× — high leverage). Measure compile-time effect on one file.

**T1 — tree-specific consolidation (the old P0/P1/P2, now the dogfooding track).**
Migrate SetRebalanceLeft onto the shared tactics (~245 lines); merge
`wp_guard_isblack_true/false`; collapse `wp_unfold_node`/`'`/`treeR_node_unfold`
(have them apply the lemma); derive `treeR_node_valid` from `treeR_node_nonnull`.
This both cleans the tree layer AND is the primary evidence for whether the generic
tactics (G1/G2) actually compose.

Rationale: G1–G4 build/validate the reusable deliverable; T1 stresses it by re-using
it across two mirror proofs. Do G1 first (smallest, highest generality, touches every
proof file → immediate reuse signal). Each step = one ~30-min validating rebuild of
the affected file(s); always prototype the tactic in a ~3s scratch first.

## EXECUTION LOG

### G1 — wp_open_func: DONE (pending final rebalance rebuild confirm)
Added `wp_open_func` and `wp_open_func_mod modpf` to WpTactics.v (Layer 3, generic
— only [func_ok]/[wp_func_intro], no hardcoded hyp names beyond the fresh
Q/vals/"Hspec" it introduces). Migrated 6 proofs' prologues:
- FindSpec (`wp_open_func`, no MODULE) ✓ 0 err
- IsBlackSpec is_black_ok + is_red_ok (`wp_open_func_mod MODULE`) ✓ 0 err
- InsertSpec (`wp_open_func_mod MODULE`) ✓ 0 err
- SetRebalanceLeft / SetRebalanceRight (`wp_open_func_mod MODULE`) — rebuild pending
InsSpec left as-is: its `iLöb as "IH"` sits between the iSplit bullet and iIntros,
so it doesn't fit the bundled tactic; a `wp_open_func_lob` variant could cover it
later (InsSpec is WIP/Admitted anyway).

**BUILD-RACE LESSON:** never run two `coqc` builds concurrently by hand when they
share/overwrite `.vo` files — I kicked off SRL/SRR while the fast-files chain was
still rewriting IsBlackSpec.vo, giving "inconsistent assumptions over library" and
a half-written .vo. Use `make -jN` (which orders by deps) for parallelism, or run
manual builds strictly serially. After a race, rebuild the chain serially to
recover.
