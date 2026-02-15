(** * FindNode Specification and Proof — DRAFT (DO NOT USE)

    !! WARNING !!

    This file is a DRAFT that proves properties about a HAND-TRANSCRIBED
    copy of the C++ AST, NOT the actual cpp2v-generated code. The
    [findNode_body] and [findNode_func] definitions below were manually
    written by reading [map_int_int_cpp.v] and copying the AST with
    substitutions ([t711] → [Tptr _Node], [Field (field_name.Id "key")]
    → [(Nid "key")], etc.). There is NO proof that this hand-written
    AST matches the actual generated translation unit.

    As a result, [findNode_ok] proves nothing about the real C++ code.
    It only proves that the hand-written copy satisfies the spec.

    This file is retained as a reference for:
    - The proof technique (loop invariant, magic wand zipper pattern)
    - The BRiCk tactic sequences (how to unfold [func_ok], process
      [Sdecl], apply [wp_while_inv], handle [nd_seq], etc.)
    - The [findNode_spec] definition (which IS reusable)
    - The helper lemmas ([findNode_lt], [findNode_gt], [treeR_leaf_implies_null])

    A correct proof must extract the function from [map_int_int_cpp.source]'s
    symbol table, not hand-copy it. See CLAUDE.md for the rule.

    ====================================================================

    Original description (for context on proof strategy):

    [findNode] is a static read-only method — the simplest operation to
    verify. The C++ version uses a while loop; the Coq spec uses structural
    recursion. We prove equivalence via a loop invariant and [wp_while_inv].

    Loop invariant -- holds before each evaluation of the loop condition:

      Exists curr_p t_curr,
        _local rho "curr" |-> ptrR<_Node> 1$m curr_p **
        curr_p |-> treeR q t_curr **
        [| findNode k t = findNode k t_curr |] **
        (curr_p |-> treeR q t_curr -* n |-> treeR q t)

    The magic wand captures the "zipper" of ancestor nodes. Each iteration
    unfolds [treeR], reads [curr->key], branches, and extends the wand.

    This file uses ONLY the open-source BRiCk core library
    ([skylabs.lang.cpp.*]), NOT the proprietary [skylabs.auto] package.
*)

From Coq Require Import ZArith Bool Lia.

Require Import daedalus_rb.RBTree.

(** ** Directional recursion lemmas

    These characterize [findNode]'s branching behavior and are used
    directly in the loop body proof to re-establish the invariant.

    Proven before BRiCk imports to avoid ssreflect [rewrite] conflict. *)

(** If [k < kn], [findNode] recurses left. *)
Lemma findNode_lt : forall k c l kn vn r,
  (k < kn)%Z ->
  findNode k (Node c l kn vn r) = findNode k l.
Proof.
  intros k c l kn vn r Hlt. simpl.
  destruct (k <? kn)%Z eqn:E; [reflexivity |].
  apply Z.ltb_ge in E. lia.
Qed.

(** If [kn < k], [findNode] recurses right. *)
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

(** Neither [k < kn] nor [kn < k] implies [k = kn]. *)
Lemma findNode_eq_key : forall k kn : Z,
  ~ (k < kn)%Z -> ~ (kn < k)%Z -> k = kn.
Proof. lia. Qed.

(** ** BRiCk imports (open-source core library only)

    After pure lemmas to avoid ssreflect [rewrite] conflict.

    Uses [skylabs.lang.cpp.cpp] which re-exports:
    - [skylabs.lang.cpp.syntax]: C++ AST types
    - [skylabs.lang.cpp.semantics]: operational semantics
    - [skylabs.lang.cpp.logic]: wp axioms ([func_ok], [wp_func],
      [wp_while_inv], [wp_if], [wp_seq], etc.)
    - [skylabs.lang.cpp.specs]: [SFunction], spec notations
      ([\arg], [\prepost], [\post])
    - [skylabs.lang.cpp.parser]: translation unit, [genv_compat] *)

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.map_int_int_cpp.

(** ** Spec and proof section *)

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.

(** *** Null pointer helper

    [nullptr] cannot represent a non-leaf tree. Used in the loop exit
    case to conclude [t_curr = Leaf] when [curr_p = nullptr].

    [treeR]'s Node case includes [structR _Node_name q], which implies
    [nonnullR] -- contradicting [nullptr].

    TODO: Prove with Iris tactics once we have the proof infrastructure
    working. For now [Admitted]. *)
Lemma treeR_null q' t' : nullptr |-> treeR q' t' |-- [| t' = Leaf |].
Proof.
  destruct t'.
  - rewrite treeR_leaf. auto.
  - rewrite treeR_node.
    (* Node case: structR _Node_name q' implies nonnullR,
       contradicting nullptr. Needs manual Iris proof. *)
Admitted.

(** *** Helper: Leaf tree forces null pointer *)
Lemma treeR_leaf_implies_null q' (p : ptr) :
  p |-> treeR q' (Leaf (K:=Z) (V:=Z)) |-- [| p = nullptr |].
Proof. rewrite treeR_leaf _at_as_Rep. auto. Qed.

(** *** Function specification

    [findNode] is a static method on [DDL::Map<int,int>::Node], so
    there is no [\this] argument -- both parameters are explicit.

    The tree is borrowed via fractional permission [q] ([\prepost] frame):
    unchanged across the call.

    Return value: [nullptr] when key absent, non-null when present.

    Constructed manually with [SFunction] (replacing the proprietary
    [cpp.spec] command from [skylabs.auto]).

    Types from the cpp2v-generated AST ([map_int_int_cpp.v]):
    - Return type: [Tptr _Node] (= [t711] in AST)
    - Param types: [Tint] for [k], [Tptr _Node] for [n]
    - Calling convention: [CC_C], arity: [Ar_Definite] *)

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

(** *** C++ function body — WRONG: hand-transcribed, not from actual AST

    !! THIS IS THE ROOT PROBLEM WITH THIS FILE !!

    This AST was hand-copied from [map_int_int_cpp.v] lines 93219-93258
    with manual substitutions:
    - [t711] replaced with [Tptr _Node]
    - [Field (field_name.Id "key")] replaced with [(Nid "key")]
    - etc.

    These substitutions may or may not be definitionally equal. Even if
    they are, there is no proof connecting [findNode_func] below to the
    actual function stored in [map_int_int_cpp.source]. The proof
    [findNode_ok] therefore proves nothing about the real C++ code.

    A correct approach must look up the function in [source]'s symbol
    table or prove that this hand-written version equals the generated one. *)

#[local] Open Scope pstring_scope.
Definition findNode_body : Stmt :=
  Sseq (
    (Sdecl (
      (Dvar "curr" (Tptr _Node)
        (Some
          (Ecast Cl2r (Evar "n" (Tptr _Node))))) :: nil)) ::
    (Swhile None
      (Ebinop Bneq
        (Ecast Cl2r (Evar "curr" (Tptr _Node)))
        (Ecast (Cnull2ptr (Tptr _Node)) Enull) Tbool)
      (Sseq (
        (Sif None
          (Ebinop Blt
            (Ecast Cl2r (Evar "k" Tint))
            (Ecast Cl2r
              (Emember true
                (Ecast Cl2r (Evar "curr" (Tptr _Node)))
                (Nid "key") false Tint)) Tbool)
          (Sexpr
            (Eassign (Evar "curr" (Tptr _Node))
              (Ecast Cl2r
                (Emember true
                  (Ecast Cl2r (Evar "curr" (Tptr _Node)))
                  (Nid "left") false (Tptr _Node)))
              (Tptr _Node)))
          (Sif None
            (Ebinop Blt
              (Ecast Cl2r
                (Emember true
                  (Ecast Cl2r (Evar "curr" (Tptr _Node)))
                  (Nid "key") false Tint))
              (Ecast Cl2r (Evar "k" Tint)) Tbool)
            (Sexpr
              (Eassign (Evar "curr" (Tptr _Node))
                (Ecast Cl2r
                  (Emember true
                    (Ecast Cl2r (Evar "curr" (Tptr _Node)))
                    (Nid "right") false (Tptr _Node)))
                (Tptr _Node)))
            (Sreturn_val
              (Ecast Cl2r (Evar "curr" (Tptr _Node)))))) :: nil))) ::
    (Sreturn_val
      (Ecast (Cnull2ptr (Tptr _Node)) Enull)) :: nil).

Definition findNode_func : Func :=
  {| f_return := Tptr _Node
   ; f_params := ("k", Tint) :: ("n", Tptr _Node) :: nil
   ; f_cc := CC_C
   ; f_arity := Ar_Definite
   ; f_exception := exception_spec.MayThrow
   ; f_body := Some (Impl findNode_body) |}.
#[local] Close Scope pstring_scope.

(** *** Proof obligation — WRONG: proves properties of the hand-copy above

    This proves [func_ok source findNode_func findNode_spec] where
    [findNode_func] is the hand-written copy, NOT the actual function
    from [source]. This proof is only useful as a reference for the
    tactic sequences; it does not verify the real C++ code. *)

Lemma findNode_ok :
  |-- func_ok map_int_int_cpp.source findNode_func findNode_spec.
Proof using MOD.
  rewrite /func_ok.
  iSplit.
  - (** Type agreement: [type_of_spec findNode_spec =
         type_of_value (Ofunction findNode_func)].
         Should reduce to equality of function types. *)
    iPureIntro. reflexivity.
  - (** Spec implies wp. *)
    iIntros "!>" (Q vals) "Hspec".
    iApply wp_func_intro.
    (** After [wp_func_intro], the goal is [wp_func' false] applied to
        our concrete function. Simplify to expose [bind_vars] + [wp]. *)
    rewrite /findNode_func /=.
    (** [Hspec] is in the spatial context from line 277. The goal is
        [match vals with [p; p0] => wp ... | _ => ERROR end].
        Extract existentials from [Hspec] to learn [vals = [pv; pv0]],
        then the match simplifies. *)
    iDestruct "Hspec" as (pv v pv0 v0) "(%Hvals & Hpk & Hpn & Hspec)".
    subst vals. simpl.
    (** Now in the [pv; pv0] case. Extract user-level spec resources. *)
    iDestruct "Hspec" as (k n q t) "(%Hargs & Htree & Hcont)".
    injection Hargs as Hv Hv0. subst v v0.
    (** Now we have concrete resources:
        - [Hpk : pv |-> tptsto_fuzzyR Tint 1 (Vint k)]
        - [Hpn : pv0 |-> tptsto_fuzzyR (Tptr _Node) 1 (Vptr n)]
        - [Htree : n |-> treeR q t]
        - [Hcont : postcondition continuation]
        Goal: [▷ wp source ρ findNode_body (Kreturn ...)]
        where ρ binds "k" → pv, "n" → pv0. *)
    (** Phase D: process the function body.
        Strip later, then enter the Sseq. *)
    iNext.
    iApply wp_seq.
    (** Now: [wp_block ρ [Sdecl [...]; Swhile ...; Sreturn ...] K].
        Unfold [wp_block] for the [Sdecl] case. *)
    rewrite wp_block_eq /wp_block_def.
    (** Now: [wp_decls ρ [Dvar "curr" ... (Some init)] (λ ρ free, ...)].
        Unseal and simplify [wp_decls]. *)
    rewrite wp_decls_eq /wp_decls_def /=.
    (** Strip fancy update [|={⊤}=>], later [▷]. *)
    iModIntro. iNext.
    (** Now: [∀ addr, qual_norm (wp_initialize_unqualified ...) (Tptr _Node) addr init Q].
        Introduce the fresh address for [curr]. *)
    iIntros (curr_p).
    (** [qual_norm] strips type qualifiers.  For [Tptr _Node] (no qualifiers),
        it passes through to [wp_initialize_unqualified]. *)
    rewrite /qual_norm /=.
    (** Unseal [wp_initialize_unqualified] for [Tptr _Node] case.
        This gives: [letI* v, free := wp_operand ρ init in
                      curr_p |-> tptsto_fuzzyR ... v -* Q free]. *)
    rewrite wp_initialize_unqualified.unlock /=.
    (** Goal: [wp_operand ρ (Ecast Cl2r (Evar "n" (Tptr _Node))) (λ v free, ...)].
        Apply l2r cast axiom, then variable lookup. *)
    iApply wp_operand_cast_l2r.
    (** Goal: [wp_glval ρ (Evar "n" ...) (λ a free, ∃ v, ...)].
        [wp_glval] dispatches to [wp_lval] for lvalue expressions. *)
    rewrite /wp_glval /=.
    (** Apply variable lookup axiom. *)
    iApply wp_lval_var.
    (** [_local ρ "n"] computes to [pv0]; [read_decl pv0 (Tptr _Node)] for
        non-reference type simplifies to the continuation applied to [pv0].
        Goal: [∃ v, (∃ q, pv0 |-> initializedR ... q v ∗ True) ∧ (wand)]. *)
    rewrite /read_decl /_local /=.
    (** Goal: [reference_to (Tptr _Node) pv0 ∗
               ∃ v, (∃ q, pv0 |-> initializedR ... q v ∗ True) ∧ (wand)].
        First, observe [reference_to] and [has_type] from [Hpn] before
        consuming it. *)
    iDestruct (observe (reference_to _ _) with "Hpn") as "#Href".
    (** Derive [has_type (Vptr n) (Tptr _Node)] from [Hpn] via observe.
        [has_type_or_undef v ty = has_type v ty ∨ v = Vundef];
        discriminate the [Vundef] case. *)
    iAssert (has_type (Vptr n) (Tptr (Tnamed _Node_name)))%I as "#Hht".
    { iDestruct (observe (has_type_or_undef _ _) with "Hpn") as "#Hty".
      iRevert "Hty". rewrite has_type_or_undef_unfold.
      iIntros "[H | %Habs]"; [iExact "H" | discriminate]. }
    iFrame "Href".
    iExists (Vptr n).
    iSplit.
    { (** Left of ∧: [∃ q, pv0 |-> initializedR ... q (Vptr n) ∗ True]. *)
      iExists (cQp.m 1).
      rewrite _at_initializedR.
      iFrame "Hpn Hht". }
    (** Right of ∧: [curr_p |-> tptsto_fuzzyR ... -∗ interp ...]. *)
    iIntros "Hcurr".
    (** [interp source FreeTemps.id P = |={⊤}=> P]. *)
    rewrite interp_unfold /=.
    (** Strip modalities one by one until we reach the wp. *)
    iModIntro. iModIntro.
    (** Goal: [|={⊤}▷=> |={⊤}▷=> wp ...].
        [|={⊤}▷=>] is the step modality. Strip with iModIntro. *)
    (** Strip remaining modalities to reach the while loop. *)
    iModIntro. iNext. do 4 iModIntro.
    (** === Phase E: Apply [wp_while_inv] ===

        The invariant captures the entire spatial context:
        - Local variable [curr] storing [Vptr cv]
        - Parameters [k] (at [pv]) and [n] (at [pv0])
        - Current subtree [cv |-> treeR q tc]
        - Functional correspondence [findNode k t = findNode k tc]
        - Magic wand (zipper): given back [tc], reconstruct full tree [t]
        - Postcondition handler [Hcont]: connects to caller's [Q]

        [Kloop] passes [ReturnVal] through to the outer continuation,
        so [Hcont] must be inside the invariant for the "found" [return]
        case. It is also needed after loop exit for [return nullptr]. *)
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
    { (** Inductive step: [I ⊢ while_unroll ρ None test body (Kloop (|> I) K)].
          [while_unroll] unfolds to [wp ρ (Sif None test body Sbreak) (Kloop (|> I) K)].

          Overview of the three control flow paths:
          1. [curr = nullptr] → test false → [Sbreak] → loop exit via [K Normal]
          2. [k < curr->key] → descend left, re-establish [|> I]
          3. [curr->key < k] → descend right, re-establish [|> I]
          4. [k = curr->key] → found → [Sreturn_val curr] → [K (ReturnVal p)] *)
      iIntros "HI".
      iDestruct "HI" as (cv tc)
        "(Hcurr & Hpk & Hpn & Htree_cv & %Hcorr & Hwand & Hcont)".
      (** [while_unroll] = [wp ρ (Sif None test body Sbreak)].
          Apply the [Sif] wp axiom. *)
      rewrite /while_unroll.
      iApply (wp_if source).
      (** Goal should be: [|> wp_test source ρ test (fun c free => ...)].
          Strip the later modality. *)
      iNext.
      (** Now process the test expression:
            [Ebinop Bneq (Ecast Cl2r (Evar "curr" _)) (Ecast (Cnull2ptr _) Enull) "bool"]

          Next steps (Phase F):
          1. [iApply (wp_operand_binop source)] to decompose the binary op
          2. Handle [nd_seq] (non-deterministic evaluation order):
             both orderings are equivalent for pure pointer reads
          3. Evaluate left operand: [Ecast Cl2r (Evar "curr" _)] → reads [cv]
          4. Evaluate right operand: [Ecast (Cnull2ptr _) Enull] → [Vptr nullptr]
          5. [eval_binop Bneq]: use [eval_ptr_neq] + [eval_ptr_eq] + [ptr_comparable]
          6. Branch on [is_true]:
             - [true]  ([cv <> nullptr]): process inner if-else + Kloop
             - [false] ([cv = nullptr]): process Sbreak → K Normal (loop exit)

          Key axioms needed (all in core library):
          - [wp_operand_binop source] (expr.v) — binary op decomposition
          - [wp_operand_cast_null source] (expr.v) — nullptr literal
          - [wp_operand_cast_l2r source] (expr.v) — l2r cast (read local)
          - [eval_ptr_neq] (operator.v) — pointer ≠ comparison
          - [treeR_null] — [nullptr |-> treeR q t ⊢ [| t = Leaf |]]

          For the inner if-else ([k < curr->key]):
          - [wp_lval_member source] (expr.v) — field access
          - [wp_lval_assign source] (expr.v) — assignment [curr = curr->left]
          - [wp_return source] (stmt.v) — [return curr] in the found case *)
      (** Step 1: Decompose [Ebinop Bneq] via [wp_operand_binop]. *)
      iApply (wp_operand_binop source).
      (** Goal: [nd_seq (wp_operand lhs) (wp_operand rhs) (fun '(v1,v2) free => ...)].
          [nd_seq] = [P //\\ Q] — prove both evaluation orderings. *)
      rewrite /nd_seq.
      (** [nd_seq] unfolds to [//\\] (bi_and): prove both eval orderings. *)
      iSplit.
      + (** Left ordering: evaluate [curr] first, then [nullptr]. *)
        (** Read [curr]: [Ecast Cl2r (Evar "curr" (Tptr _Node))]. *)
        iApply wp_operand_cast_l2r.
        rewrite /wp_glval /=.
        iApply wp_lval_var.
        rewrite /read_decl /_local /=.
        (** Need [reference_to] and [has_type] from [Hcurr]. *)
        iDestruct (observe (reference_to _ _) with "Hcurr") as "#Href_cv".
        iFrame "Href_cv".
        iExists (Vptr cv).
        iSplit.
        { (** Prove value exists at [curr_p]. *)
          iExists (cQp.m 1).
          rewrite _at_initializedR.
          iDestruct (observe (has_type_or_undef _ _) with "Hcurr") as "#Hty_cv".
          iRevert "Hty_cv". rewrite has_type_or_undef_unfold.
          iIntros "[H | %Habs]"; [| discriminate].
          iFrame "Hcurr". iExact "H". }
        (** Right of [//\\]: continue with [v1 = Vptr cv].
            [Hcurr] is still available (both branches of [//\\] get
            the full spatial context in affine BI).
            Now evaluate [nullptr]: [Ecast (Cnull2ptr _) Enull]. *)
        iApply wp_operand_cast_null; [reflexivity | reflexivity |].
        iApply wp_null.
        (** Now at [eval_binop] + [wp_test] continuation:
              [Exists v', (eval_binop ... v' ** True) //\\
                match is_true v' with Some c => K c free | None => ERROR end]
            Case-split on subtree to determine the comparison result. *)
        destruct tc as [| c_tc l_tc kn_tc vn_tc r_tc].
        ++ (** Leaf: [cv = nullptr], comparison yields false → [Sbreak]. *)
           iDestruct (treeR_leaf_implies_null with "Htree_cv") as "%Hnull".
           subst cv.
           iExists (Vbool false). rewrite /Vbool /=.
           iSplit.
           { (** [eval_binop Bneq (Vptr nullptr) (Vptr nullptr) (Vint 0)] *)
             admit. }
           (** [Sbreak] via [Kloop] → [K Normal] → return nullptr.
               Leaf means [findNode k t = None] (from Hcorr).
               TODO: process Sbreak, Kloop, Kseq, Sreturn_val. *)
           admit.
        ++ (** Node: [cv <> nullptr], comparison yields true → body. *)
           iExists (Vbool true). rewrite /Vbool /=.
           iSplit.
           { (** [eval_binop Bneq (Vptr cv) (Vptr nullptr) (Vint 1)] *)
             admit. }
           (** Strip [interp source (1 >*> 1)] wrapper.
               [1 >*> 1] = [FreeTemps.seq id id], unfolds via [interp_unfold]
               to [|={⊤}=> |={⊤}=> wp ...]. *)
           do 2 rewrite interp_unfold. iModIntro.
           (** Enter [Sseq [Sif ...]]. *)
           iApply wp_seq.
           rewrite wp_block_eq /wp_block_def.
           (** Strip [|={⊤}=> |={⊤}▷=> ...] = [|={⊤}=> |={⊤}=> ▷ |={⊤}=> ...]. *)
           do 2 iModIntro. iNext. iModIntro.
           (** Now: [wp ρ' (Sif None test thn els) (Kseq (wp_block []) (|={⊤}=> K))].
               Apply [wp_if] for the inner test [k < curr->key]. *)
           iApply (wp_if source).
           iNext.
           (** Now: [wp_test] (auto-unfolds to [wp_operand]) of:
                 [Ebinop Blt (Ecast Cl2r (Evar "k" Tint))
                             (Ecast Cl2r (Emember true (Evar "curr" _) "key" _ Tint))
                             Tbool]
               Three branches after evaluating and case-splitting:
               1. [k < kn_tc] → [curr = curr->left], continue loop
               2. [kn_tc < k] → inner else → [curr = curr->right], continue loop
               3. [k = kn_tc] → inner else else → [return curr]
               TODO: Phase F.2 — evaluate test, branch, complete. *)
           admit.
      + (** Right ordering: evaluate [nullptr] first, then [curr]. *)
        admit. }
    (** Establish the invariant from the current spatial resources.
        Initial values: [cv = n] (curr starts at n), [tc = t] (full tree). *)
    iExists n, t.
    iFrame "Hcurr Hpk Hpn Htree Hcont".
    iSplitR.
    { iPureIntro. reflexivity. }
    (** Magic wand: identity wand [n |-> treeR q t -* n |-> treeR q t]. *)
    iIntros "H". iExact "H".
Admitted.

End with_Sigma.
