(** * Tree-Specific Tactics and Lemmas for BRiCk wp Proofs
    Created: 2026-02-15
    Updated: 2026-02-17 — Split generic tactics to [WpTactics.v].

    Re-exports all generic wp tactics from [WpTactics.v] and adds
    tree-specific lemmas and tactics tied to [treeR] / [_Node].

    == Lemmas ==

    - [treeR_node_nonnull] — Extract [p <> nullptr] from [treeR (Node ...)].
    - [treeR_node_valid] — Extract [valid_ptr p] from [treeR (Node ...)].
    - [treeR_node_fold] — Reconstruct [treeR (Node ...)] from fields.

    == Tactics ==

    - [wp_unfold_node H] — Destructure [treeR (Node ...)] into field hypotheses.
*)

Require Export daedalus_rb.WpTactics.
Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.

(** ** Tree node observation lemmas

    These lemmas extract persistent/pure facts from [treeR (Node ...)]
    without consuming the tree hypothesis. They replace a 15-line
    unfold → observe → refold pattern with a single [iDestruct]. *)

Section tree_lemmas.
Context `{Sigma : cpp_logic} {CU : genv}.

(** Extract [p <> nullptr] from [treeR q (Node ...)].

    Usage:
<<
      iDestruct (treeR_node_nonnull with "Htree") as "[Htree %Hne]".
>>
*)
Lemma treeR_node_nonnull q c l k v r (p : ptr) :
  p |-> treeR q (Node c l k v r) |--
    p |-> treeR q (Node c l k v r) ** [| p <> nullptr |].
Proof.
  rewrite treeR_node _at_as_Rep.
  iIntros "H".
  iDestruct "H" as (lp rp rc) "(Htl & Htr & Hnode)".
  iDestruct "Hnode" as "(Hrc & Hcolor & Hkey & Hval & Hleft & Hright & Hstruct)".
  iDestruct (observe (p |-> nonnullR) with "Hstruct") as "#Hnn".
  iSplitL.
  - iExists lp, rp, rc. iFrame.
  - iRevert "Hnn". rewrite _at_nonnullR. auto.
Qed.

(** Extract [valid_ptr p] from [treeR q (Node ...)].

    Usage:
<<
      iDestruct (treeR_node_valid with "Htree") as "[Htree #Hvalid]".
>>
*)
Lemma treeR_node_valid q c l k v r (p : ptr) :
  p |-> treeR q (Node c l k v r) |--
    p |-> treeR q (Node c l k v r) ** valid_ptr p.
Proof.
  rewrite treeR_node _at_as_Rep.
  iIntros "H".
  iDestruct "H" as (lp rp rc) "(Htl & Htr & Hnode)".
  iDestruct "Hnode" as "(Hrc & Hcolor & Hkey & Hval & Hleft & Hright & Hstruct)".
  iDestruct (observe (p |-> validR) with "Hstruct") as "#Hv".
  iSplitL.
  - iExists lp, rp, rc. iFrame.
  - iRevert "Hv". rewrite _at_validR. auto.
Qed.

(** Fold field assertions back into [treeR (Node ...)].

    This is the inverse of the unfold done by [_at_as_Rep] + [iDestruct].
    After mutating fields in InsertSpec.v, use this to re-establish
    the [treeR] invariant.

    Usage:
<<
      iApply (treeR_node_fold with "[$Htl $Htr $Hrc $Hcolor $Hkey $Hval $Hleft $Hright $Hstruct]").
>>
*)
Lemma treeR_node_fold q c l k v r (lp rp : ptr) (rc : Z) (p : ptr) :
  lp |-> treeR q l **
  rp |-> treeR q r **
  p |-> (_ref_count |-> ulongR q rc **
         _color     |-> boolR q (color_to_bool c) **
         _key       |-> intR q k **
         _value     |-> intR q v **
         _left      |-> ptrR<_Node> q lp **
         _right     |-> ptrR<_Node> q rp **
         structR _Node_name q) |--
  p |-> treeR q (Node c l k v r).
Proof.
  rewrite treeR_node _at_as_Rep.
  iIntros "(Htl & Htr & Hnode)".
  iExists lp, rp, rc. iFrame.
Qed.

End tree_lemmas.

(** ** [wp_unfold_node H] — Destructure [treeR (Node ...)] into fields

    [H] names the Iris hypothesis holding [p |-> treeR q (Node c l k v r)].

    After the tactic, the context contains:
    - [_ntl], [_ntr]: child subtree representations ([lp |-> treeR q l] etc.)
    - [_nrc], [_ncolor], [_nkey], [_nval], [_nleft], [_nright]: field assertions
    - [_nstruct]: struct identity assertion ([structR _Node_name q])
    - Fresh Coq variables for the child pointers [lp], [rp] and ref count [rc].

    This replaces the 3-line unfold pattern:
<<
      iRevert H. rewrite _at_as_Rep. iIntros H.
      iDestruct H as (lp rp rc) "(Htl & Htr & Hnode)".
      iDestruct "Hnode" as "(Hrc & Hcolor & Hkey & Hval & Hleft & Hright & Hstruct)".
>>

    After the tactic, rename hypotheses with [iRename] as needed.
    To reconstruct the tree afterward, use [treeR_node_fold].
*)
Ltac wp_unfold_node H :=
  iRevert H; rewrite _at_as_Rep; iIntros H;
  let lp := fresh "_lp" in
  let rp := fresh "_rp" in
  let rc := fresh "_rc" in
  iDestruct H as (lp rp rc) "(_ntl & _ntr & _nnode)";
  iDestruct "_nnode" as
    "(_nrc & _ncolor & _nkey & _nval & _nleft & _nright & _nstruct)".

(** Convert [tptstoR] back to [primR] and revert offset in one step.

    After mutating a tree field via assignment, [wp_lval_assign] yields
    [(p ,, f) |-> tptstoR ty q v]. To reconstruct [treeR (Node ...)] via
    [treeR_node_fold], we need [p |-> (f |-> primR ty q v)]. This tactic:
    1. Applies [tptstoR_to_primR] (requires [~~ is_raw_or_undef v])
    2. Reverts the offset ([(p ,, f) |-> R] → [p |-> (f |-> R)])

    [H_src] names the source hypothesis ([tptstoR] at offset form).
    [H_dst] names the destination hypothesis (useful for renaming,
    e.g. ["_ncolor_new"] → ["_ncolor"]).
    [v] is the concrete value (e.g. [Vbool false]).
    [Hpure] is a proof of [~~ is_raw_or_undef v] (typically [I]).

    Usage:
<<
      wp_field_to_primR "_ncolor_new" "_ncolor" (Vbool false) I.
>>
*)
Ltac wp_field_to_primR H_src H_dst v Hpure :=
  iPoseProof (tptstoR_to_primR _ _ _ v Hpure with H_src) as H_dst;
  wp_revert_offset H_dst.
