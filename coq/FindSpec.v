(** * FindNode Specification and Proof

    Proves that the C++ [Node::findNode] function refines the functional
    [findNode] from [RBTree.v].

    Unlike FindSpec_draft.v (which proved properties of a hand-transcribed
    AST copy), this file extracts the function DIRECTLY from the cpp2v-
    generated translation unit [map_int_int_cpp.source] via symbol table
    lookup. The extraction is machine-checked by [native_compute].

    == Approach ==

    1. Construct [findNode_name] — the symbol table key for the function.
    2. Look up [findNode_name] in [source.(symbols)] to get the actual [Func].
    3. Prove the lookup succeeds via [native_compute; reflexivity].
    4. State [func_ok source findNode_func findNode_spec].
    5. Prove using wp tactics (reusing techniques from FindSpec_draft.v).
*)

From Coq Require Import ZArith Bool Lia.

Require Import daedalus_rb.RBTree.

(** ** Directional recursion lemmas (reused from FindSpec_draft.v) *)

Lemma findNode_lt : forall k c l kn vn r,
  (k < kn)%Z ->
  findNode k (Node c l kn vn r) = findNode k l.
Proof.
  intros k c l kn vn r Hlt. simpl.
  destruct (k <? kn)%Z eqn:E; [reflexivity |].
  apply Z.ltb_ge in E. lia.
Qed.

Lemma findNode_gt : forall k c l kn vn r,
  (kn < k)%Z ->
  findNode k (Node c l kn vn r) = findNode k r.
Proof.
  intros k c l kn vn r Hgt. simpl.
  destruct (k <? kn)%Z eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (kn <? k)%Z eqn:E2; [reflexivity |].
    apply Z.ltb_ge in E2. lia.
Qed.

Lemma findNode_eq_key : forall k kn : Z,
  ~ (k < kn)%Z -> ~ (kn < k)%Z -> k = kn.
Proof. lia. Qed.

(** ** BRiCk imports *)

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.Tactics.
Require Import daedalus_rb.map_int_int_cpp.

(** ** Function extraction from the actual generated AST

    We construct the symbol table key [findNode_name] and extract the
    function via computation. This is the manual equivalent of the
    proprietary [cpp.spec "name" from source] command.

    [findNode] is a static method ([Dmethod n12334 true] in the generated
    AST), so [parser.v:194] stores it as [Ofunction (static_method m)]
    in the symbol table.

    The name [n12334] (local to the generated file) expands to:
      [Nscoped _Node_name (Nfunction function_qualifiers.N "findNode"
                            (Tint :: Tptr _Node :: nil))]
*)

#[local] Open Scope pstring_scope.
Definition findNode_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "findNode"
      (Tint :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

(** Extract the actual function from the symbol table. The [match] on
    the lookup result is a computational extraction — [findNode_func]
    will reduce to the actual [Func] value stored in [source]. The
    fallback branch is unreachable (proven by [findNode_lookup]). *)
Definition findNode_func : Func :=
  match source.(symbols) !! findNode_name with
  | Some (Ofunction f) => f
  | _ =>
    {| f_return := Tvoid
     ; f_params := nil
     ; f_cc := CC_C
     ; f_arity := Ar_Definite
     ; f_exception := exception_spec.NoThrow
     ; f_body := None |}
  end.

(** Machine-checked proof that the lookup succeeds. If this compiles,
    [findNode_name] correctly identifies our function in the AST. *)
Lemma findNode_lookup :
  source.(symbols) !! findNode_name = Some (Ofunction findNode_func).
Proof. native_compute. reflexivity. Qed.

(** ** Spec and proof *)

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.

Lemma treeR_null q' t' : nullptr |-> treeR q' t' |-- [| t' = Leaf |].
Proof.
  destruct t'.
  - rewrite treeR_leaf. auto.
  - rewrite treeR_node _at_as_Rep.
    iIntros "H".
    iDestruct "H" as (lp rp rc) "(Htl & Htr & Hnode)".
    (** Decompose the [_at] over [∗] to isolate [structR], then
        derive a contradiction from [nonnullR] at [nullptr]. *)
    iDestruct "Hnode" as "(Hrc & Hcolor & Hkey & Hval & Hleft & Hright & Hstruct)".
    iDestruct (observe (nullptr |-> nonnullR) with "Hstruct") as "Hnn".
    rewrite _at_nonnullR.
    by iDestruct "Hnn" as %[].
Qed.

Lemma treeR_leaf_implies_null q' (p : ptr) :
  p |-> treeR q' (Leaf (K:=Z) (V:=Z)) |-- [| p = nullptr |].
Proof. rewrite treeR_leaf _at_as_Rep. auto. Qed.

Definition findNode_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node) (Tint :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node) (Tint :: Tptr _Node :: nil)
      (\arg{k} "k" (Vint k)
       \arg{n} "n" (Vptr n)
       \prepost{q t} n |-> treeR q t
       \post{ret}[Vptr ret]
         [| match findNode k t with
            | None   => ret = nullptr
            | Some _ => ret <> nullptr
            end |])).

Lemma findNode_ok :
  |-- func_ok source findNode_func findNode_spec.
Proof using MOD.
  rewrite /func_ok.
  iSplit.
  - iPureIntro. reflexivity.
  - iIntros "!>" (Q vals) "Hspec".
    iApply wp_func_intro.
    (** Simplify: expose bind_vars + wp body.
        [findNode_func] is extracted from the symbol table, so [/=] must
        compute through the match on [source.(symbols) !! findNode_name].
        This may require [vm_compute] or explicit unfolding if [/=] is
        too slow. *)
    rewrite /findNode_func /=.
    (** Extract existentials from Hspec to learn vals structure. *)
    iDestruct "Hspec" as (pv v pv0 v0) "(%Hvals & Hpk & Hpn & Hspec)".
    subst vals. simpl.
    iDestruct "Hspec" as (k n q t) "(%Hargs & Htree & Hcont)".
    injection Hargs as Hv Hv0. subst v v0.
    (** Strip later, enter Sseq, unfold block + decl. *)
    wp_auto.
    iIntros (curr_p).
    wp_auto.
    wp_read_local "Hpn" (Vptr n).
    iIntros "Hcurr".
    wp_auto.
    (** Apply wp_while_inv with magic-wand loop invariant. *)
    iApply (wp_while_inv source (
      Exists (cv : ptr) (tc : tree Z Z),
        curr_p |-> tptsto_fuzzyR (Tptr _Node) (cQp.m 1) (Vptr cv) **
        pv |-> tptsto_fuzzyR Tint (cQp.m 1) (Vint k) **
        pv0 |-> tptsto_fuzzyR (Tptr _Node) (cQp.m 1) (Vptr n) **
        cv |-> treeR q tc **
        [| findNode k t = findNode k tc |] **
        (cv |-> treeR q tc -* n |-> treeR q t) **
        (Forall ret : ptr,
          n |-> treeR q t **
          [| match findNode k t with
             | Some _ => ret <> nullptr
             | None => ret = nullptr
             end |] -*
          Forall ra : ptr,
            pv |-> anyR Tint (cQp.m 1) **
            pv0 |-> anyR (Tptr _Node) (cQp.m 1) **
            ra |-> tptsto_fuzzyR (Tptr _Node) (cQp.m 1) (Vptr ret) -*
            Q ra))%I).
    { (** Inductive step: [I ⊢ while_unroll ...]. *)
      iIntros "HI".
      iDestruct "HI" as (cv tc)
        "(Hcurr & Hpk & Hpn & Htree_cv & %Hcorr & Hwand & Hcont)".
      rewrite /while_unroll.
      iApply (wp_if source).
      iNext.
      (** Decompose [Ebinop Bneq] via [wp_operand_binop]. *)
      iApply (wp_operand_binop source).
      rewrite /nd_seq.
      iSplit.
      + (** Left ordering: evaluate [curr] first, then [nullptr]. *)
        wp_read_local "Hcurr" (Vptr cv).
        (** Evaluate [nullptr]. *)
        wp_null_val.
        (** Case-split on subtree structure. *)
        destruct tc as [| c_tc l_tc kn_tc vn_tc r_tc].
        ++ (** Leaf: [cv = nullptr], comparison yields false → [Sbreak]. *)
           iDestruct (treeR_leaf_implies_null with "Htree_cv") as "%Hnull".
           subst cv.
           iExists (Vbool false). rewrite /Vbool /=.
           iSplit.
           { (** [eval_binop Bneq (Vptr nullptr) (Vptr nullptr) (Vint 0) ∗ True]
                 Strategy: build [eval_binop_impure ... ∗ True] via pointer
                 equality lemmas, then embed into [eval_binop] disjunction. *)
             iPoseProof valid_ptr_nullptr as "Hvn".
             iPoseProof (eval_ptr_self_eq source _Node nullptr with "Hvn")
               as "Heq".
             iPoseProof (eval_ptr_neq source _Node nullptr nullptr true
               with "Heq") as "[Himpure Htrue]".
             rewrite /eval_binop.
             iFrame "Htrue". iRight. iExact "Himpure". }
           (** Break from loop, process [return curr;] (= return nullptr). *)
           wp_auto.
           iIntros (ret_p).
           (** Return expression: [Ecast Cnull2ptr Enull] = nullptr. *)
           wp_auto.
           (** Wand: [ret_p |-> tptsto_fuzzyR ... (Vptr nullptr) -* ...]. *)
           iIntros "Hret_store".
           (** Process interp, Kfree/Kreturn, reach destruction. *)
           wp_auto.
           (** Destroy [curr_p] local variable (primitive pointer type). *)
           wp_destroy_local "Hcurr".
           (** Now prove [▷ Q ret_p] using invariant resources. *)
           iNext.
           (** Reconstruct the tree via magic wand. *)
           iAssert (nullptr |-> treeR q Leaf)%I as "Htree_leaf".
           { rewrite treeR_leaf _at_as_Rep. auto. }
           iDestruct ("Hwand" with "Htree_leaf") as "Htree".
           (** Apply postcondition handler [Hcont] with ret=nullptr, ra=ret_p. *)
           iApply ("Hcont" $! nullptr with "[Htree]").
           { iFrame "Htree". iPureIntro. rewrite Hcorr. reflexivity. }
           iFrame "Hret_store".
           (** Need [pv |-> anyR Tint 1$m ** pv0 |-> anyR (Tptr _Node) 1$m].
               Convert tptsto_fuzzyR to anyR via entailment. *)
           iSplitL "Hpk".
           { wp_finish_anyR. }
           wp_finish_anyR.
        ++ (** Node: [cv <> nullptr], comparison yields true → body. *)
           (** Extract [valid_ptr cv] and [cv ≠ nullptr] from [treeR (Node ...)]. *)
           iDestruct (treeR_node_nonnull with "Htree_cv") as "[Htree_cv %Hcv_ne]".
           iDestruct (treeR_node_valid with "Htree_cv") as "[Htree_cv #Hvalid_cv]".
           iExists (Vbool true). rewrite /Vbool /=.
           iSplit.
           { (** [eval_binop Bneq (Vptr cv) (Vptr nullptr) (Vbool true) ∗ True]
                 Use [eval_ptr_nullptr_eq_l]: cv ≠ nullptr (from nonnullR)
                 and valid_ptr cv (from structR) to show Beq yields false,
                 then eval_ptr_neq flips to Bneq yields true (negb false). *)
             iPoseProof (eval_ptr_nullptr_eq_l source
               (fun _ : is_Some (ptr_vaddr cv) =>
                  bool_decide_eq_false_2 (cv = nullptr) Hcv_ne)
               with "Hvalid_cv") as "Heq".
             iPoseProof (eval_ptr_neq source _Node cv nullptr false
               with "Heq") as "[Himpure Htrue]".
             rewrite /eval_binop.
             iFrame "Htrue". iRight. iExact "Himpure". }
           (** Strip [interp] + enter [Sseq [Sif ...]]. *)
           wp_auto.
           (** Inner [Sif]: test [k < curr->key]. *)
           iApply (wp_if source).
           iNext.
           (** Unfold [treeR (Node ...)] to access fields. *)
           wp_unfold_node "Htree_cv".
           (** Evaluate [k < curr->key] via [wp_operand_binop]. *)
           iApply (wp_operand_binop source).
           rewrite /nd_seq.
           iSplit.
           { (** Left ordering: eval [k], then [curr->key]. *)
             wp_read_local "Hpk" (Vint k).
             (** Now eval [curr->key]. *)
             admit. }
           (** Right ordering: symmetric. *)
           admit.
      + (** Right ordering: symmetric to left. *)
        admit. }
    (** Establish invariant. *)
    iExists n, t.
    iFrame "Hcurr Hpk Hpn Htree Hcont".
    iSplitR.
    { iPureIntro. reflexivity. }
    iIntros "H". iExact "H".
Admitted.

End with_Sigma.
