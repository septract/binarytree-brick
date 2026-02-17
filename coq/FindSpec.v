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

(** ** Shared continuations for [nd_seq] orderings

    Each [wp_operand_binop] produces [nd_seq] = [∧], requiring both
    left and right operand orderings. After evaluation, the goal is
    identical — these tactics capture the shared continuation so
    each ordering just evaluates its operands and calls the tactic.

    Coq-term variables (cv, kn_tc, etc.) must be explicit parameters
    since they exist only in the proof context, not at definition time.
    Iris hypothesis names (strings like "Hcurr") are resolved at call
    time and don't need parameterization. *)

(** Read [curr->key] via field access chain. *)
Ltac findNode_read_curr_key cv kn_tc :=
  wp_member_access;
  wp_read_local "Hcurr" (Vptr cv);
  wp_observe_ref "_nstruct";
  rewrite /read_decl /=;
  wp_offset "_nkey";
  (* Extract has_type_prop for kn_tc as a pure Coq hypothesis.
     After wp_offset, _nkey is [p |-> primR Tint q (Vint kn_tc)].
     The instance [primR_observe_has_type_prop] + [_at_observe_only_provable]
     gives [Observe [| has_type_prop (Vint kn_tc) Tint |] (p |-> primR ...)].
     Idempotent: skip if already present (this tactic is called twice
     in the same proof branch — once for the outer comparison and once
     for the inner comparison). *)
  match goal with
  | _ : has_type_prop (Vint kn_tc) Tint |- _ => idtac
  | _ =>
    iDestruct (observe ([| has_type_prop (Vint kn_tc) Tint |]) with "_nkey")
      as "%_htp_kn"
  end;
  wp_observe_ref "_nkey";
  wp_provide_value "_nkey" (Vint kn_tc).

(** Innermost continuation: after evaluating both operands of [curr->key < k].
    Case-splits on [kn_tc < k]: go-right or break (key found). *)
Ltac findNode_after_inner2_eval kn_tc k cv n q t _lp _rp _rc r_tc :=
  iExists (Vbool (bool_decide (kn_tc < k)%Z));
  iSplit;
  [ wp_eval_int_lt "_hty_k"
  | rewrite /Vbool /=;
    destruct (bool_decide (kn_tc < k)%Z) eqn:Hgt;
    [ (* kn_tc < k: go right *)
      wp_auto;
      iApply wp_lval_assign;
      rewrite /=;
      wp_member_access;
      wp_read_local "Hcurr" (Vptr cv);
      wp_struct_field "_nstruct" "_nright" (Vptr _rp);
      wp_assign_local "Hcurr";
      iIntros "Hcurr_new";
      wp_auto;
      iExists _rp, r_tc;
      iDestruct (tptstoR_to_fuzzyR with "Hcurr_new") as "Hcurr_new";
      iFrame "Hcurr_new Hpk Hpn _ntr";
      iSplitR;
      [ iPureIntro;
        match goal with Hc : findNode _ _ = findNode _ _ |- _ => rewrite Hc end;
        apply findNode_gt;
        match goal with Hg : bool_decide (kn_tc < k)%Z = true |- _ =>
          apply bool_decide_eq_true_1 in Hg; exact Hg end
      | iSplitL "Hwand _ntl _nrc _ncolor _nkey _nval _nleft _nright _nstruct";
        [ iIntros "Htr_back";
          iApply "Hwand";
          wp_revert_offset "_nkey";
          wp_revert_offset "_nright";
          iExists _lp, _rp, _rc;
          iFrame "_ntl Htr_back";
          iFrame "_nrc _ncolor _nkey _nval _nleft _nright _nstruct"
        | iExact "Hcont" ] ]
    | (* k = kn_tc: break *)
      wp_auto;
      let ret_p := fresh "ret_p" in
      iIntros (ret_p);
      wp_read_local "Hcurr" (Vptr cv);
      iIntros "Hret_store";
      wp_auto;
      wp_destroy_local "Hcurr";
      iNext;
      wp_revert_offset "_nkey";
      iAssert (n |-> treeR q t)%I
        with "[Hwand _ntl _ntr _nrc _ncolor _nkey _nval _nleft _nright _nstruct]"
        as "Htree";
      [ iApply "Hwand";
        iExists _lp, _rp, _rc;
        iFrame "_ntl _ntr _nrc _ncolor _nkey _nval _nleft _nright _nstruct"
      | iApply ("Hcont" $! cv with "[Htree]");
        [ iFrame "Htree"; iPureIntro;
          match goal with Hc : findNode _ _ = findNode _ _ |- _ => rewrite Hc end;
          simpl;
          match goal with Hl : bool_decide (k < kn_tc)%Z = false |- _ =>
            apply bool_decide_eq_false_1 in Hl end;
          match goal with Hg : bool_decide (kn_tc < k)%Z = false |- _ =>
            apply bool_decide_eq_false_1 in Hg end;
          destruct (k <? kn_tc)%Z eqn:E1;
          [ apply Z.ltb_lt in E1; lia
          | destruct (kn_tc <? k)%Z eqn:E2;
            [ apply Z.ltb_lt in E2; lia
            | assumption ] ]
        | iFrame "Hret_store";
          iSplitL "Hpk"; [wp_finish_anyR | wp_finish_anyR] ] ] ] ].

(** Inner continuation: after evaluating both operands of [k < curr->key].
    Case-splits on [k < kn_tc]: go-left or else-branch (inner comparison). *)
Ltac findNode_after_inner1_eval kn_tc k cv n q t _lp _rp _rc l_tc r_tc :=
  iExists (Vbool (bool_decide (k < kn_tc)%Z));
  iSplit;
  [ wp_eval_int_lt "_hty_k"
  | rewrite /Vbool /=;
    destruct (bool_decide (k < kn_tc)%Z) eqn:Hlt;
    [ (* k < kn_tc: go left *)
      wp_auto;
      iApply wp_lval_assign;
      rewrite /=;
      wp_member_access;
      wp_read_local "Hcurr" (Vptr cv);
      wp_struct_field "_nstruct" "_nleft" (Vptr _lp);
      wp_assign_local "Hcurr";
      iIntros "Hcurr_new";
      wp_auto;
      iExists _lp, l_tc;
      iDestruct (tptstoR_to_fuzzyR with "Hcurr_new") as "Hcurr_new";
      iFrame "Hcurr_new Hpk Hpn _ntl";
      iSplitR;
      [ iPureIntro;
        match goal with Hc : findNode _ _ = findNode _ _ |- _ => rewrite Hc end;
        apply findNode_lt;
        match goal with Hl : bool_decide (k < kn_tc)%Z = true |- _ =>
          apply bool_decide_eq_true_1 in Hl; exact Hl end
      | iSplitL "Hwand _ntr _nrc _ncolor _nkey _nval _nleft _nright _nstruct";
        [ iIntros "Htl_back";
          iApply "Hwand";
          wp_revert_offset "_nkey";
          wp_revert_offset "_nleft";
          iExists _lp, _rp, _rc;
          iFrame "Htl_back _ntr";
          iFrame "_nrc _ncolor _nkey _nval _nleft _nright _nstruct"
        | iExact "Hcont" ] ]
    | (* k >= kn_tc: inner comparison [curr->key < k] *)
      wp_auto;
      iApply (wp_if source); iNext;
      wp_revert_offset "_nkey";
      wp_binop source
        ltac:(findNode_read_curr_key cv kn_tc)
        ltac:(wp_read_local "Hpk" (Vint k))
        ltac:(findNode_after_inner2_eval kn_tc k cv n q t _lp _rp _rc r_tc) ] ].

(** Outer continuation: after evaluating both operands of [curr != nullptr].
    Case-splits on [tc]: Leaf (exit loop) or Node (enter body). *)
Ltac findNode_after_outer_eval cv tc k n q t :=
  destruct tc as [| c_tc l_tc kn_tc vn_tc r_tc];
  [ (* Leaf: cv = nullptr, loop exits *)
    iDestruct (treeR_leaf_implies_null with "Htree_cv") as "%Hnull";
    subst;
    iExists (Vbool false); rewrite /Vbool /=;
    iSplit;
    [ wp_eval_ptr_neq_null source _Node
    | wp_auto;
      let ret_p := fresh "ret_p" in
      iIntros (ret_p);
      wp_auto;
      iIntros "Hret_store";
      wp_auto;
      wp_destroy_local "Hcurr";
      iNext;
      iAssert (nullptr |-> treeR q Leaf)%I as "Htree_leaf";
      [ rewrite treeR_leaf _at_as_Rep; auto
      | iDestruct ("Hwand" with "Htree_leaf") as "Htree";
        iApply ("Hcont" $! nullptr with "[Htree]");
        [ iFrame "Htree"; iPureIntro;
          match goal with Hc : findNode _ _ = findNode _ _ |- _ => rewrite Hc end;
          reflexivity
        | iFrame "Hret_store";
          iSplitL "Hpk"; [wp_finish_anyR | wp_finish_anyR] ] ] ]
  | (* Node: cv ≠ nullptr, enter loop body *)
    iDestruct (treeR_node_nonnull with "Htree_cv") as "[Htree_cv %Hcv_ne]";
    iDestruct (treeR_node_valid with "Htree_cv") as "[Htree_cv #Hvalid_cv]";
    iExists (Vbool true); rewrite /Vbool /=;
    iSplit;
    [ wp_eval_ptr_neq_nonnull source _Node "Hvalid_cv"
    | wp_auto;
      iApply (wp_if source); iNext;
      (* Inline wp_unfold_node so variable bindings stay in Ltac scope *)
      iRevert "Htree_cv"; rewrite _at_as_Rep; iIntros "Htree_cv";
      let lp := fresh "_lp" in
      let rp := fresh "_rp" in
      let rc := fresh "_rc" in
      iDestruct "Htree_cv" as (lp rp rc) "(_ntl & _ntr & _nnode)";
      iDestruct "_nnode" as
        "(_nrc & _ncolor & _nkey & _nval & _nleft & _nright & _nstruct)";
      (* Extract persistent has_type for [k] before operand evaluation
         consumes the spatial resources. This persists through all nested
         [iSplit]s and is available at each [eval_binop] goal.
         The [kn_tc] evidence is extracted inside [findNode_read_curr_key]
         after [wp_offset] flattens the nested [_at]. *)
      iDestruct (observe (has_type_or_undef (Vint k) Tint) with "Hpk") as "#_hty_k";
      wp_binop source
        ltac:(wp_read_local "Hpk" (Vint k))
        ltac:(findNode_read_curr_key cv kn_tc)
        ltac:(findNode_after_inner1_eval kn_tc k cv n q t lp rp rc l_tc r_tc) ] ].

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
      (** Decompose [Ebinop Bneq] via [wp_binop].
          Both orderings share [findNode_after_outer_eval]. *)
      wp_binop source
        ltac:(wp_read_local "Hcurr" (Vptr cv))
        ltac:(wp_null_val)
        ltac:(findNode_after_outer_eval cv tc k n q t). }
    (** Establish invariant. *)
    iExists n, t.
    iFrame "Hcurr Hpk Hpn Htree Hcont".
    iSplitR.
    { iPureIntro. reflexivity. }
    iIntros "H". iExact "H".
Qed.

End with_Sigma.
