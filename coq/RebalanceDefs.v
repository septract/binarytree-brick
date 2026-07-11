(** * Shared definitions for the setRebalanceLeft/Right refinement proofs.

    Split out of the former monolithic [RebalanceSpec.v] so that the two ~1000-line
    proofs [setRebalanceLeft_ok] (SetRebalanceLeft.v) and [setRebalanceRight_ok]
    (SetRebalanceRight.v) compile in SEPARATE files — editing one no longer
    rebuilds the other, and [make -j] builds them in parallel. See
    docs/notes/2026-07-10_rebalance_perf_plan.md. This file holds:
    - the pure [setRebalanceLeft/Right_default] rewrite lemmas;
    - the guard-opener tactics [wp_guard_isblack_true/false], parameterised by the
      module proof [modpf] so they need no section-local [MODULE] and can be used
      from either proof file. *)
From Stdlib Require Import ZArith Bool Lia.

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.Tactics.
Require Import daedalus_rb.InsertDefs.
(* Real is_black_ok / is_red_ok proofs (InsertDefs.v has only Admitted stubs). *)
Require Import daedalus_rb.IsBlackSpec.

(* ================================================================= *)
(** * Pure helper lemmas (no cpp_logic context) *)
(* ================================================================= *)

(** ** Default-case helper: [setRebalanceLeft c newL k v r = Node c newL k v r]
    when neither LL nor LR rotation applies:
    - [c = Red] (any newL); [c = Black, newL = Leaf];
    - [c = Black, newL = Node Black _ _ _ _];
    - [c = Black, newL = Node Red (non-Red) _ _ (non-Red)]. *)
Lemma setRebalanceLeft_default (c : Color) (newL : tree Z Z) (k : Z) (v : Z) (r : tree Z Z) :
  ~ (c = Black /\ exists a kx vx b ky vy c1,
       newL = Node Red (Node Red a kx vx b) ky vy c1) ->
  ~ (c = Black /\ exists a kx vx b ky vy c1,
       newL = Node Red a kx vx (Node Red b ky vy c1)) ->
  setRebalanceLeft c newL k v r = Node c newL k v r.
Proof.
  intros Hno_ll Hno_lr.
  unfold setRebalanceLeft.
  destruct c; [reflexivity |].
  destruct newL as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    try reflexivity;
    solve [
      exfalso; apply Hno_ll; split; [reflexivity |]; do 7 eexists; reflexivity
    | exfalso; apply Hno_lr; split; [reflexivity |]; do 7 eexists; reflexivity
    ].
Qed.

(** ** Analogous for setRebalanceRight *)
Lemma setRebalanceRight_default (c : Color) (l : tree Z Z) (k : Z) (v : Z) (newR : tree Z Z) :
  ~ (c = Black /\ exists b ky vy c1 kz vz d,
       newR = Node Red (Node Red b ky vy c1) kz vz d) ->
  ~ (c = Black /\ exists b ky vy c1 kz vz d,
       newR = Node Red b ky vy (Node Red c1 kz vz d)) ->
  setRebalanceRight c l k v newR = Node c l k v newR.
Proof.
  intros Hno_rl Hno_rr.
  unfold setRebalanceRight.
  destruct c; [reflexivity |].
  destruct newR as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    try reflexivity;
    solve [
      exfalso; apply Hno_rl; split; [reflexivity |]; do 7 eexists; reflexivity
    | exfalso; apply Hno_rr; split; [reflexivity |]; do 7 eexists; reflexivity
    ].
Qed.

(* ================================================================= *)
(** * Guard-opener tactics *)
(* ================================================================= *)

(** [wp_guard_isblack_true modpf np] — opener of every [c = Black] rebalance case:
    enter [Sif (Eseqand (is_black n) (is_red …))], evaluate [is_black(n)] to
    [true] (Black node), recover the node's [_color]/[structR]. After it,
    [Hcolor]/[Hstruct] are back and the goal is the second [Eseqand] operand
    [is_red(newX)]. [modpf] is the [|-- denoteModule source] proof (passed
    explicitly so this tactic needs no section-local [MODULE]); [np] the node ptr.
    Stable-named [HMOD Hpn Hstruct Hcolor]. Generic over left/right. *)
Ltac wp_guard_isblack_true modpf np :=
  let ret := fresh "ret" in
  let rx := fresh "rx" in
  iApply (wp_if source); iNext;
  rewrite /wp.WPE.wp_test /=;
  iApply wp_operand_seqand;
  rewrite /wp.WPE.wp_test /=;
  wp_operand_call_direct1 "HMOD" is_black_lookup is_black_has_body
    is_black_name (is_black_ok modpf) is_black_func
    "Hpn" (Vptr np) "Hstruct";
  rewrite /is_black_spec /=;
  iExists _, (Vptr np);
  iSplit; [ iPureIntro; reflexivity |];
  iSplitL "Hargp"; [ iFrame "Hargp" |];
  iExists np, (Some Black), (cQp.m 1);
  iSplit; [ iPureIntro; reflexivity |];
  iSplitL "Hcolor Hstruct"; [ rewrite _at_sep /=; iFrame "Hcolor Hstruct" |];
  iIntros (ret) "Hpost";
  iIntros (rx) "(Hany & Hres)";
  wp_auto;
  wp_destroy_prim_temp "Hany";
  iModIntro; rewrite operand_receive.unlock /=;
  iExists (Vbool true);
  iFrame "Hres";
  simpl;
  iDestruct "Hpost" as "[Hpost _]";
  rewrite _at_sep /=;
  iDestruct "Hpost" as "[Hcolor Hstruct]".

(** [wp_guard_isblack_false modpf np] — the [c = Red] opener (both rebalance fns):
    [is_black(n)] = [false] SHORT-CIRCUITS the [Eseqand] (no [is_red] call); then
    recover [_color]/[structR] and land on the [Sif] else (default) branch. *)
Ltac wp_guard_isblack_false modpf np :=
  let ret := fresh "ret" in
  let rx := fresh "rx" in
  iApply (wp_if source); iNext;
  rewrite /wp.WPE.wp_test /=;
  iApply wp_operand_seqand;
  rewrite /wp.WPE.wp_test /=;
  wp_operand_call_direct1 "HMOD" is_black_lookup is_black_has_body
    is_black_name (is_black_ok modpf) is_black_func
    "Hpn" (Vptr np) "Hstruct";
  rewrite /is_black_spec /=;
  iExists _, (Vptr np);
  iSplit; [ iPureIntro; reflexivity |];
  iSplitL "Hargp"; [ iFrame "Hargp" |];
  iExists np, (Some Red), (cQp.m 1);
  iSplit; [ iPureIntro; reflexivity |];
  iSplitL "Hcolor Hstruct"; [ rewrite _at_sep /=; iFrame "Hcolor Hstruct" |];
  iIntros (ret) "Hpost";
  iIntros (rx) "(Hany & Hres)";
  wp_auto;
  wp_destroy_prim_temp "Hany";
  iModIntro; rewrite operand_receive.unlock /=;
  iExists (Vbool false);
  iFrame "Hres";
  simpl;
  iDestruct "Hpost" as "[Hpost _]";
  rewrite _at_sep /=;
  iDestruct "Hpost" as "[Hcolor Hstruct]".
