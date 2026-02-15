(** * Custom Ltac Automation for BRiCk wp Proofs
    Created: 2026-02-15

    Reusable tactics that compress repeated 4-12 line boilerplate sequences
    in wp proofs into single calls. Used by FindSpec.v, InsertSpec.v, etc.

    == Tactics ==

    - [wp_read_local H v] — Read a local variable via l2r cast.
      Replaces ~12 lines of [wp_operand_cast_l2r / wp_lval_var /
      read_decl / observe reference_to / initializedR] boilerplate.

    - [wp_null_val] — Evaluate a [nullptr] operand.
      Replaces [wp_operand_cast_null; wp_null].

    - [wp_enter_block] — Enter a [Sseq] block after [interp].
      Replaces [interp_unfold / wp_seq / wp_block_eq / iModIntro] sequence.

    - [wp_finish_anyR] — Convert [tptsto_fuzzyR] to [anyR].
      Wrapper around [anyR_tptsto_fuzzyR_val_2].
*)

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

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
