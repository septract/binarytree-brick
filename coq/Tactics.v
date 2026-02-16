(** * Custom Ltac Automation for BRiCk wp Proofs
    Created: 2026-02-15

    Reusable tactics and lemmas that compress repeated boilerplate
    in wp proofs into single calls. Used by FindSpec.v, InsertSpec.v, etc.

    == Lemmas ==

    - [treeR_node_nonnull] — Extract [p <> nullptr] from [treeR (Node ...)].
    - [treeR_node_valid] — Extract [valid_ptr p] from [treeR (Node ...)].

    == Tactics ==

    - [wp_read_local H v] — Read a local variable via l2r cast (~12 lines → 1).
    - [wp_null_val] — Evaluate a [nullptr] operand (2 lines → 1).
    - [wp_enter_block] — Enter a [Sseq] block after [interp] (4 lines → 1).
    - [wp_finish_anyR] — Convert [tptsto_fuzzyR] to [anyR].
    - [wp_destroy_local H] — Destroy a local variable of primitive type (~8 lines → 1).
*)

From Coq Require Import ZArith.

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.

(** ** [wp_null_val] — Evaluate a nullptr operand

    Replaces:
<<
      iApply wp_operand_cast_null; [reflexivity | reflexivity |].
      iApply wp_null.
>>
*)
Ltac wp_null_val :=
  iApply wp_operand_cast_null; [reflexivity | reflexivity |];
  iApply wp_null.

(** ** [wp_enter_block] — Enter a Sseq block after interp

    Replaces:
<<
      do 2 rewrite interp_unfold. iModIntro.
      iApply wp_seq.
      rewrite wp_block_eq /wp_block_def.
      do 2 iModIntro. iNext. iModIntro.
>>
*)
Ltac wp_enter_block :=
  do 2 rewrite interp_unfold; iModIntro;
  iApply wp_seq;
  rewrite wp_block_eq /wp_block_def;
  do 2 iModIntro; iNext; iModIntro.

(** ** [wp_finish_anyR] — Convert tptsto_fuzzyR to anyR

    Replaces:
<<
      by rewrite anyR_tptsto_fuzzyR_val_2.
>>

    Useful as a semantic wrapper when cleaning up parameter ownership
    at function return. *)
Ltac wp_finish_anyR :=
  by rewrite anyR_tptsto_fuzzyR_val_2.

(** ** [wp_read_local H v] — Read a local variable via l2r cast

    [H] is a string naming the Iris hypothesis holding the [tptsto_fuzzyR]
    for the local variable. [v] is the value stored in it (e.g. [Vint k]
    or [Vptr n]).

    Replaces the ~12 line pattern:
<<
      iApply wp_operand_cast_l2r.
      rewrite /wp_glval /=.
      iApply wp_lval_var.
      rewrite /read_decl /_local /=.
      iDestruct (observe (reference_to _ _) with H) as "#Href".
      iFrame "Href".
      iExists v.
      iSplit.
      { iExists (cQp.m 1).
        rewrite _at_initializedR.
        iDestruct (observe (has_type_or_undef _ _) with H) as "#Hty".
        iRevert "Hty". rewrite has_type_or_undef_unfold.
        iIntros "[H' | %Habs]"; [| discriminate].
        iFrame H. iExact "H'". }
>>

    After the tactic, the current goal is the continuation after
    reading the variable.

    Note: uses fixed temporary hypothesis names [_ref] and [_hty]
    for the persistent [observe] results. [_ref] is cleared after
    use so the tactic can be called multiple times without name
    clashes. [_hty] is consumed by [iRevert] and doesn't persist.
*)
Ltac wp_read_local H v :=
  iApply wp_operand_cast_l2r;
  rewrite /wp_glval /=;
  iApply wp_lval_var;
  rewrite /read_decl /_local /=;
  iDestruct (observe (reference_to _ _) with H) as "#_ref";
  iFrame "_ref";
  iClear "_ref";
  iExists v;
  iSplit;
  [ iExists (cQp.m 1);
    rewrite _at_initializedR;
    iDestruct (observe (has_type_or_undef _ _) with H) as "#_hty";
    iRevert "_hty"; rewrite has_type_or_undef_unfold;
    iIntros "[_htmp | %_habs]";
    [ iFrame H; iExact "_htmp"
    | discriminate ]
  | ].

(** ** [wp_destroy_local H] — Destroy a local variable of primitive type

    [H] is the hypothesis name holding [tptsto_fuzzyR] for the local.

    Replaces the ~8 line pattern:
<<
      destroy_val_unfold.
      rewrite wp_destroy_prim.unlock /=.
      iModIntro.
      iSplitL H.
      { iRevert H. rewrite _at_tptsto_fuzzyR.
        iIntros "(%v' & %Hrel & Htpsto)".
        iExists v'. rewrite _at_tptstoR. iExact "Htpsto". }
>>

    After the tactic, the remaining goal is the continuation
    (typically [▷ Q ret_p]).
*)
Ltac wp_destroy_local H :=
  destroy_val_unfold;
  rewrite wp_destroy_prim.unlock /=;
  iModIntro;
  iSplitL H;
  [ iRevert H; rewrite _at_tptsto_fuzzyR;
    iIntros "_dtmp";
    let v := fresh "_dv" in
    iDestruct "_dtmp" as (v) "[% _dtpsto]";
    iExists v; rewrite _at_tptstoR; iExact "_dtpsto"
  | ].

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

End tree_lemmas.
