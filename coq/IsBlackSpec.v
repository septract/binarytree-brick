(** * is_black / is_red refinement proofs — Phase B *)
From Stdlib Require Import ZArith Bool Lia.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.
Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.Tactics.
Require Import daedalus_rb.InsertDefs.

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.
Hypothesis MODULE : |-- denoteModule source.

Lemma is_black_ok :
  |-- func_ok source is_black_func is_black_spec.
Proof using MOD MODULE.
  rewrite /func_ok. iSplit.
  - iPureIntro. reflexivity.
  - iIntros "!>" (Q vals) "Hspec".
    iPoseProof MODULE as "#HMOD".
    iApply wp_func_intro.
    rewrite /is_black_func /=.
    iDestruct "Hspec" as (pn vn) "(%Hvals & Hpn & Hspec)".
    subst vals. simpl.
    iDestruct "Hspec" as (n_ptr c_opt) "(%Hargs & Hpre & Hcont)".
    injection Hargs as ->. subst.
    wp_auto.
    iIntros (p).
    iApply wp_operand_seqor.
    rewrite /wp.WPE.wp_test /=.
    (** LHS: evaluate [n == nullptr] as a pointer Beq. *)
    destruct c_opt as [c |].
    + (** Some c: n_ptr <> nullptr, so LHS is false; then evaluate RHS. *)
      iDestruct "Hpre" as (q) "[Hcolor Hstruct]".
      iDestruct (observe (n_ptr |-> nonnullR) with "Hstruct") as "#Hnn".
      iDestruct (observe (n_ptr |-> validR) with "Hstruct") as "#Hvld".
      rewrite _at_nonnullR. iDestruct "Hnn" as "%Hne".
      iRevert "Hvld". rewrite _at_validR. iIntros "#Hvld".
      (** LHS [n == nullptr] evaluates to [false] (both operand orders via
          [wp_binop], which swaps [eval_a]/[eval_b] between the two orderings). *)
      wp_binop source
        ltac:(wp_read_local "Hpn" (Vptr n_ptr))
        ltac:(wp_null_val)
        ltac:(iExists (Vbool false);
              iSplit;
              [ iSplitR; [| done];
                rewrite /eval_binop; iRight;
                iPoseProof (eval_ptr_nullptr_eq_l source (res := false)
                  (fun _ : is_Some (ptr_vaddr n_ptr) =>
                     bool_decide_eq_false_2 (n_ptr = nullptr) Hne)
                  with "Hvld") as "_peq";
                iDestruct "_peq" as "[_pimp _]"; iExact "_pimp"
              | simpl;
                (** RHS: [(int)n->color == (int)false]. Witnesses stay symbolic
                    ([color_to_bool c]); the [eval_eq] and [kont] closers each
                    [destruct c] locally, with the whole post-[destruct] block
                    parenthesised so its brackets apply per-branch (not across
                    the doubled goal set). Casts via
                    [wp_operand_cast_integral]+[conv_int] (bool→int keeps the bool
                    value); integer [Beq] via [eval_eq]. *)
                wp_binop source
                  ltac:((* (int)(n->color): read the field, cast keeps bool *)
                        iApply wp_operand_cast_integral;
                        wp_member_access;
                        wp_read_local "Hpn" (Vptr n_ptr);
                        wp_struct_field "Hstruct" "Hcolor" (Vbool (color_to_bool c));
                        iExists (Vbool (color_to_bool c));
                        iSplit; [ iPureIntro; rewrite /conv_int /=;
                                  (split; [ apply has_type_prop_bool; eauto
                                          | by destruct (color_to_bool c) ]) | ])
                  ltac:((* (int)false *)
                        iApply wp_operand_cast_integral;
                        iApply wp_operand_bool;
                        iExists (Vbool false);
                        iSplit; [ iPureIntro; rewrite /conv_int /=;
                                  (split; [ apply has_type_prop_bool; eauto | done ]) | ])
                  ltac:(iExists (Vbool (match c with Red => false | Black => true end));
                        iSplit;
                        [ iSplitR; [| done];
                          rewrite /eval_binop; iLeft; iPureIntro;
                          destruct c; simpl;
                          ( eapply eval_eq;
                            [ typeclasses eauto | done
                            | apply has_int_type; rewrite /bitsize.bound /=; lia
                            | apply has_int_type; rewrite /bitsize.bound /=; lia ] )
                        | simpl; iIntros "Hret"; repeat wp_step;
                          destruct c; simpl;
                          ( wp_revert_offset "Hcolor";
                            iPoseProof ("Hcont" $! p with "[Hcolor Hstruct]") as "Hc";
                            [ iSplitL; [ iExists q; rewrite _at_sep; iFrame "Hcolor Hstruct" | done ]
                            | iApply ("Hc" $! p with "[Hpn Hret]");
                              iFrame "Hret";
                              rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] ] ) ]) ]).
    + (** None: n_ptr = nullptr, LHS is true → return Vbool true. *)
      iDestruct "Hpre" as "%Hnull". subst n_ptr.
      (** Evaluate the pointer Beq: n(=nullptr) == nullptr → true. [wp_binop]
          discharges both [nd_seq] operand orders (swapping [eval_a]/[eval_b]);
          they reach the same [kont]. *)
      wp_binop source
        ltac:(wp_read_local "Hpn" (Vptr nullptr))
        ltac:(wp_null_val)
        ltac:(iExists (Vbool true);
              iSplit;
              [ (* eval_binop Beq nullptr nullptr = true: peel True, impure
                   branch, close with eval_ptr_self_eq *)
                iSplitR; [| done];
                rewrite /eval_binop; iRight;
                iPoseProof valid_ptr_nullptr as "_pvn";
                iPoseProof (eval_ptr_self_eq _ _ nullptr with "_pvn") as "_peq";
                iDestruct "_peq" as "[_pimp _]"; iExact "_pimp"
              | (* is_true (Vbool true) = Some true → return Vbool true *)
                simpl; iIntros "Hret"; repeat wp_step;
                iPoseProof ("Hcont" $! p with "[]") as "Hc";
                [ iSplitR; [ iPureIntro; reflexivity | done ]
                | iApply ("Hc" $! p with "[Hpn Hret]");
                  iFrame "Hret";
                  rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] ] ]).
Qed.

End with_Sigma.
