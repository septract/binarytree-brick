(** * Custom Ltac Automation for BRiCk wp Proofs
    Created: 2026-02-15

    Reusable tactics and lemmas that compress repeated boilerplate
    in wp proofs into single calls. Used by FindSpec.v, InsertSpec.v, etc.

    == Lemmas ==

    - [treeR_node_nonnull] — Extract [p <> nullptr] from [treeR (Node ...)].
    - [treeR_node_valid] — Extract [valid_ptr p] from [treeR (Node ...)].
    - [treeR_node_fold] — Reconstruct [treeR (Node ...)] from fields.

    == Tactics ==

    - [wp_read_local H v] — Read a local variable via l2r cast (~12 lines → 1).
    - [wp_null_val] — Evaluate a [nullptr] operand (2 lines → 1).
    - [wp_enter_block] — Enter a [Sseq] block after [interp] (4 lines → 1).
    - [wp_finish_anyR] — Convert [tptsto_fuzzyR] to [anyR].
    - [wp_destroy_local H] — Destroy a local variable of primitive type (~8 lines → 1).
    - [wp_unfold_node H] — Destructure [treeR (Node ...)] into field hypotheses (3 lines → 1).
    - [wp_offset H] — Convert [p |-> (f |-> R)] to [(p ,, f) |-> R] (~3 lines → 1).
    - [wp_provide_value H v] — Provide [initializedR] evidence from [primR] (~8 lines → 1).
    - [wp_member_access] — Structural prefix for [ptr->field] access (4 lines → 1).
    - [wp_struct_field H_struct H_field v] — Observe + offset + provide value (8 lines → 1).
    - [wp_binop tu eval_a eval_b kont] — Deduplicate [nd_seq] orderings (6+ lines → 1).
    - [wp_expr_step] — Expression-level AST dispatcher (experimental).
    - [wp_step] — One mechanical wp proof step (AST-driven dispatch).
    - [wp_auto] — Repeat [wp_step] until stuck (user provides only semantic steps).
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

(** Observe [reference_to (Tnamed cls) p] from [p |-> structR cls q].

    Chain: structR → type_ptrR (observe) → svalidR (observe) →
    strict_valid_ptr (_at_svalidR) → reference_to_intro + has_type_ptr'
    (valid_ptr via strict_valid_valid, aligned_ptr_ty via
    type_ptr_aligned_pure).

    Registered as [Observe] so [observe] can extract [reference_to]
    persistently without consuming the [structR] hypothesis.

    Usage:
<<
      iDestruct (observe (reference_to _ _) with "_nstruct") as "#_ref_cv".
>>
*)
Local Lemma structR_reference_to_entails cls q (p : ptr) :
  p |-> structR cls q |-- reference_to (Tnamed cls) p.
Proof.
  iIntros "H".
  iDestruct (observe (p |-> type_ptrR (Tnamed cls)) with "H") as "#Htype".
  iDestruct (observe (p |-> svalidR) with "Htype") as "#Hsvalid".
  iClear "H".
  iRevert "Hsvalid". rewrite _at_svalidR. iIntros "#Hsvalid".
  iPoseProof (reference_to_intro with "Hsvalid") as "Hwand".
  iApply "Hwand".
  rewrite has_type_ptr'.
  iPoseProof (strict_valid_valid with "Hsvalid") as "#Hvalid".
  iFrame "Hvalid".
  iRevert "Htype". rewrite _at_type_ptrR. iIntros "#Htype".
  by iPoseProof (type_ptr_aligned_pure with "Htype") as "$".
Qed.

#[global] Instance structR_reference_to cls q (p : ptr) :
  Observe (reference_to (Tnamed cls) p) (p |-> structR cls q).
Proof.
  rewrite /Observe.
  etransitivity; [exact (structR_reference_to_entails cls q p) |].
  iIntros "#H". iModIntro. iExact "H".
Qed.

(** One-directional entailment for [_at_offsetR], used by [wp_offset].
    [_at_offsetR] is a bi-entailment ([equiv]) which can't be rewritten
    in contravariant position. This lemma provides the forward direction
    as a plain entailment, which [iPoseProof] can apply to a hypothesis. *)
Lemma at_offsetR_intro (p : ptr) (o : offset) (r : Rep) :
  p |-> _offsetR o r |-- (p ,, o) |-> r.
Proof. by rewrite _at_offsetR. Qed.

(** One-directional entailment for [_at_primR], used by [wp_provide_value].
    Decomposes [primR] into its pure, persistent, and spatial components
    as a plain entailment. *)
Lemma at_primR_intro (p : ptr) ty q v :
  p |-> primR ty q v |--
    [| ~~ is_raw v |] ** has_type v ty ** p |-> tptsto_fuzzyR ty q v.
Proof. by rewrite _at_primR. Qed.

(** Convert [tptstoR] to [tptsto_fuzzyR] at a given pointer.

    After an assignment, [wp_lval_assign] yields [p |-> tptstoR ...].
    The loop invariant uses [p |-> tptsto_fuzzyR ...] (the weaker form).
    This lemma bridges the gap.

    Usage:
<<
      iDestruct (tptstoR_to_fuzzyR with "H") as "H".
>>
*)
Lemma tptstoR_to_fuzzyR (p : ptr) ty q v :
  p |-> tptstoR ty q v |-- p |-> tptsto_fuzzyR ty q v.
Proof. by rewrite tptsto_fuzzyR_intro. Qed.

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

(** ** [wp_offset H] — Convert [p |-> (f |-> R)] to [(p ,, f) |-> R]

    [H] names the Iris hypothesis holding [p |-> (_field |-> R)].
    After the tactic, [H] holds [(p ,, _field) |-> R].

    Uses [at_offsetR_intro] (forward direction of [_at_offsetR]) via
    [iDestruct] to transform the hypothesis in place.

    Replaces:
<<
      iAssert ((p ,, _field) |-> R)%I with "[H]" as "H".
      { by rewrite -_at_offsetR. }
>>
*)
Ltac wp_offset H :=
  iDestruct (at_offsetR_intro with H) as H.

(** ** [wp_provide_value H v] — Provide [initializedR] evidence from [primR]

    [H] names the Iris hypothesis holding [(p ,, f) |-> primR ty q v]
    (e.g. [intR q kn_tc]). [v] is the value (e.g. [Vint kn_tc]).

    Uses [at_primR_intro] (forward direction of [_at_primR]) via
    [iDestruct] to decompose the [primR] into pure, persistent, and
    spatial parts that satisfy the [initializedR] goal.

    Replaces the ~8 line pattern:
<<
      iExists v.
      iSplit.
      { iExists q.
        rewrite _at_initializedR.
        iAssert ([| ~~ is_raw v |] ** has_type v ty **
                 (p ,, f) |-> tptsto_fuzzyR ty q v)%I
          with "[H]" as "(%_Hraw & #_Htype & _Htptsto)".
        { by rewrite -_at_primR. }
        iFrame "_Htptsto".
        iExact "_Htype". }
>>

    After the tactic, [H] is consumed and the goal is the continuation
    after the value read.
*)
Ltac wp_provide_value H v :=
  iExists v;
  iSplit;
  [ iExists _;
    rewrite _at_initializedR;
    iDestruct (at_primR_intro with H) as "(%_pv_raw & #_pv_type & _pv_tptsto)";
    iFrame "_pv_tptsto"; iExact "_pv_type"
  | ].

(** ** [wp_member_access] — structural prefix for [ptr->field] access

    Handles the l2r cast → member access → arrow dereference prefix that
    appears before every field read through a pointer.  Purely structural:
    no arguments needed.

    Replaces:
<<
      iApply wp_operand_cast_l2r;
      rewrite /wp_glval /=;
      iApply wp_lval_member; [reflexivity |];
      rewrite /read_arrow /=.
>>
*)
Ltac wp_member_access :=
  iApply wp_operand_cast_l2r;
  rewrite /wp_glval /=;
  iApply wp_lval_member; [reflexivity |];
  rewrite /read_arrow /=.

(** ** [wp_struct_field H_struct H_field v] — observe + offset + provide value

    After reading the parent pointer, this handles the [reference_to] observe
    from the struct, the [read_decl] + field offset conversion, and the value
    provision.

    [H_struct] is the hypothesis for the struct identity ([structR]).
    [H_field] is the hypothesis for the field ([primR] / [ptrR]).
    [v] is the expected value (e.g. [Vptr lp]).

    Replaces:
<<
      iDestruct (observe (reference_to _ _) with H_struct) as "#_obs";
      iSplitR; [iExact "_obs" |]; iClear "_obs";
      rewrite /read_decl /=;
      wp_offset H_field;
      iDestruct (observe (reference_to _ _) with H_field) as "#_obs";
      iSplitR; [iExact "_obs" |]; iClear "_obs";
      wp_provide_value H_field v.
>>
*)
Ltac wp_struct_field H_struct H_field v :=
  iDestruct (observe (reference_to _ _) with H_struct) as "#_obs";
  iSplitR; [iExact "_obs" |]; iClear "_obs";
  rewrite /read_decl /=;
  wp_offset H_field;
  iDestruct (observe (reference_to _ _) with H_field) as "#_obs";
  iSplitR; [iExact "_obs" |]; iClear "_obs";
  wp_provide_value H_field v.

(** ** [wp_binop tu eval_a eval_b kont] — nd_seq deduplication for binops

    Every [wp_operand_binop] requires proving both operand orderings with
    identical continuations.  This tactic takes:
    - [tu]: translation unit (e.g. [source])
    - [eval_a], [eval_b]: tactic arguments evaluating each operand
    - [kont]: continuation tactic applied after both operands

    The [eval_a]/[eval_b]/[kont] arguments are passed via [ltac:(...)]:
<<
      wp_binop source
        ltac:(wp_read_local "Hcurr" (Vptr cv))
        ltac:(wp_null_val)
        ltac:(findNode_after_outer_eval cv tc k n q t).
>>

    Replaces:
<<
      iApply (wp_operand_binop source).
      rewrite /nd_seq.
      iSplit.
      + eval_a. eval_b. kont.
      + eval_b. eval_a. kont.
>>
*)
Ltac wp_binop tu eval_a eval_b kont :=
  iApply (wp_operand_binop tu);
  rewrite /nd_seq;
  iSplit; [ eval_a; eval_b; kont | eval_b; eval_a; kont ].

(** ** Meta-tactic: wp proof automation

    [wp_step] performs one mechanical wp proof step by trying rules in
    priority order. [wp_auto] repeats it until stuck.

    Design principle: [wp_auto] handles ALL mechanical/syntactic steps
    (modality stripping, AST-driven wp rules, definitional unfolding).
    The user provides ONLY semantic steps (loop invariants, case splits,
    eval_binop proofs, resource framing, hypothesis destructuring).

    Intended proof style:
<<
      wp_auto.                          (* mechanical: reach the while *)
      iApply (wp_while_inv source I).   (* semantic: provide invariant *)
      { wp_auto.                        (* mechanical: enter loop body *)
        destruct tc.                    (* semantic: case split *)
        - wp_auto. ...                  (* each branch *)
      }
>>

    == Priority order ==

    1. Statement wp rules (deterministic: match AST constructor)
    2. Block/decl/init unfolding
    3. Expression wp rules (null literal)
    4. Interp unfolding (temporary destruction)
    5. Continuation unfolding (Kloop, Kfree, etc.)
    6. Modality stripping (fallback: |={⊤}=>, ▷)

    Note: l2r cast, member access, read_arrow/read_decl are NOT included
    because they are part of larger sequences (wp_read_local, field access)
    and would interfere if auto-fired.

    Modalities are last because they appear between every other step —
    if tried first, they'd mask the actual wp rule that should fire.
    But wp rules only apply when modalities have been stripped. The
    [repeat] loop handles this: first pass strips modalities, second
    pass finds the wp rule.
*)

Ltac wp_step :=
  first [
    (* 1. Statement-level wp rules *)
    iApply wp_seq |
    iApply wp_break |
    iApply wp_return |
    iApply wp_expr |
    (* 2. Block / declaration / initialization unfolding *)
    progress (rewrite wp_block_eq /wp_block_def) |
    progress (rewrite wp_decls_eq /wp_decls_def /=) |
    progress (rewrite /wp_initialize /qual_norm /=) |
    progress (rewrite wp_initialize_unqualified.unlock /=) |
    (* 3. Expression-level rules *)
    progress (rewrite /wp_discard /=) |
    wp_null_val |
    (* 4. Interp (temporary destruction) unfolding *)
    progress (rewrite interp_unfold /=) |
    (* 5. Continuation structure unfolding *)
    progress (rewrite /while_unroll) |
    progress (rewrite /Kloop /Kloop_inner /=) |
    progress (rewrite /Kfree /Kat_exit /Kcleanup /Kreturn /Kreturn_inner /=) |
    progress (rewrite /get_return_type /=) |
    (* 6. Modality stripping (fallback) *)
    progress iModIntro |
    progress iNext
  ].

(** [wp_auto] repeats [wp_step] until the goal requires user input.
    Terminates because each step makes progress (changes the goal)
    and the AST is finite. *)
Ltac wp_auto := repeat wp_step.

(** ** [wp_expr_step] — expression-level AST dispatcher (experimental)

    Dispatches on the head AST constructor of expression-level wp goals.
    Complements [wp_step] (which handles statement-level constructs)
    without modifying that battle-tested tactic.

    Uses [lazymatch] so failures propagate immediately (no silent
    backtracking).  The [Ecast Cl2r (Evar _ _)] case only peels the
    l2r cast (needs user-supplied hypothesis name and value for the
    full [wp_read_local]).

    Note: matching on large cpp2v expressions (95K lines) may be slow.
    If [lazymatch] performance degrades, restrict to smaller pattern sets.
*)
Ltac wp_expr_step :=
  lazymatch goal with
  | |- environments.envs_entails _
       (wp_operand _ _ (Ecast Cl2r (Emember _ _ _ _ _)) _) =>
      wp_member_access
  | |- environments.envs_entails _
       (wp_operand _ _ (Ecast Cnull2ptr _) _) =>
      wp_null_val
  | |- environments.envs_entails _
       (wp_operand _ _ (Ecast Cl2r (Evar _ _)) _) =>
      (* Can't fully dispatch — needs H and v arguments.
         Just peel the l2r cast as a partial step. *)
      iApply wp_operand_cast_l2r; rewrite /wp_glval /=
  | _ => wp_step
  end.
