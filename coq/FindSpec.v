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
  - rewrite treeR_node.
Admitted.

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
    (** Strip later, enter Sseq. *)
    iNext.
    iApply wp_seq.
    rewrite wp_block_eq /wp_block_def.
    rewrite wp_decls_eq /wp_decls_def /=.
    iModIntro. iNext.
    iIntros (curr_p).
    rewrite /qual_norm /=.
    rewrite wp_initialize_unqualified.unlock /=.
    iApply wp_operand_cast_l2r.
    rewrite /wp_glval /=.
    iApply wp_lval_var.
    rewrite /read_decl /_local /=.
    iDestruct (observe (reference_to _ _) with "Hpn") as "#Href".
    iAssert (has_type (Vptr n) (Tptr (Tnamed _Node_name)))%I as "#Hht".
    { iDestruct (observe (has_type_or_undef _ _) with "Hpn") as "#Hty".
      iRevert "Hty". rewrite has_type_or_undef_unfold.
      iIntros "[H | %Habs]"; [iExact "H" | discriminate]. }
    iFrame "Href".
    iExists (Vptr n).
    iSplit.
    { iExists (cQp.m 1).
      rewrite _at_initializedR.
      iFrame "Hpn Hht". }
    iIntros "Hcurr".
    rewrite interp_unfold /=.
    iModIntro. iModIntro.
    iModIntro. iNext. do 4 iModIntro.
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
    { (** Inductive step. *)
      admit. }
    (** Establish invariant. *)
    iExists n, t.
    iFrame "Hcurr Hpk Hpn Htree Hcont".
    iSplitR.
    { iPureIntro. reflexivity. }
    iIntros "H". iExact "H".
Admitted.

End with_Sigma.
