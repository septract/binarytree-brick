(** * Generic WP Tactics for BRiCk Proofs
    Created: 2026-02-17

    Reusable tactics and lemmas for wp proofs against any C++ code.
    Contains NO tree-specific imports — purely generic BRiCk automation.

    Tree-specific items live in [Tactics.v], which re-exports this file.

    == Layer 0: Entailment Lemmas ==

    - [structR_reference_to_entails] + [Observe] instance — Extract [reference_to] from [structR].
    - [at_offsetR_intro] — Forward direction of [_at_offsetR].
    - [at_primR_intro] — Decompose [primR] into components.
    - [tptstoR_to_fuzzyR] — Weaken [tptstoR] to [tptsto_fuzzyR].

    == Layer 1: Atomic Tactics ==

    - [wp_null_val] — Evaluate a [nullptr] operand.
    - [wp_finish_anyR] — Convert [tptsto_fuzzyR] to [anyR].
    - [wp_offset H] / [wp_revert_offset H] — Nest/unnest [_at] + [_offsetR].
    - [wp_observe_ref H] — Observe [reference_to] + provide + clear.

    == Layer 2: Composite Tactics ==

    - [wp_read_local H v] — Read a local variable via l2r cast.
    - [wp_destroy_local H] — Destroy a local variable of primitive type.
    - [wp_provide_value H v] — Provide [initializedR] evidence from [primR].
    - [wp_member_access] — Structural prefix for [ptr->field] access.
    - [wp_struct_field H_struct H_field v] — Observe + offset + provide value.
    - [wp_assign_local H_local] — L-value target of [local = rhs].
    - [wp_eval_int_binop H_hty eval_lemma] — Prove [eval_binop] for integer binary ops.
    - [wp_eval_int_lt H_hty] — Alias: [wp_eval_int_binop H_hty eval_lt].
    - [wp_eval_ptr_neq_null tu cls] — Prove [nullptr != nullptr] evaluates to false.
    - [wp_eval_ptr_neq_nonnull tu cls H_valid] — Prove [cv != nullptr] evaluates to true.
    - [wp_binop tu eval_a eval_b kont] — Deduplicate [nd_seq] orderings.

    == Layer 3: Meta-Tactics ==

    - [wp_step] / [wp_auto] — Mechanical wp proof automation.
    - [wp_expr_step] — Expression-level AST dispatcher.
*)

From Coq Require Export ZArith.

Require Export skylabs.lang.cpp.cpp.
Require Export skylabs.iris.extra.proofmode.proofmode.
Export cQp_compat.

(* ================================================================= *)
(** ** Layer 0: Entailment Lemmas *)
(* ================================================================= *)

Section wp_lemmas.
Context `{Sigma : cpp_logic} {CU : genv}.

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

End wp_lemmas.

(* ================================================================= *)
(** ** Layer 1: Atomic Tactics *)
(* ================================================================= *)

(** Evaluate a nullptr operand.

    Replaces:
<<
      iApply wp_operand_cast_null; [reflexivity | reflexivity |].
      iApply wp_null.
>>
*)
Ltac wp_null_val :=
  iApply wp_operand_cast_null; [reflexivity | reflexivity |];
  iApply wp_null.

(** Convert [tptsto_fuzzyR] to [anyR].

    Replaces:
<<
      by rewrite anyR_tptsto_fuzzyR_val_2.
>>

    Useful as a semantic wrapper when cleaning up parameter ownership
    at function return. *)
Ltac wp_finish_anyR :=
  by rewrite anyR_tptsto_fuzzyR_val_2.

(** Convert [p |-> (f |-> R)] to [(p ,, f) |-> R].

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

(** Convert [(p ,, f) |-> R] back to [p |-> (f |-> R)].

    Inverse of [wp_offset]. Needed before applying magic wands that
    expect the nested-offset form (e.g. reconstructing [treeR (Node ...)]
    from individual field assertions).

    [H] names the Iris hypothesis holding [(p ,, f) |-> R].
    After the tactic, [H] holds [p |-> (f |-> R)].

    Replaces:
<<
      iRevert H; rewrite -_at_offsetR; iIntros H.
>>
*)
Ltac wp_revert_offset H :=
  iRevert H; rewrite -_at_offsetR; iIntros H.

(** Observe [reference_to] + provide + clear.

    Extracts a persistent [reference_to] fact from hypothesis [H],
    provides it to satisfy the current [iSplitR] subgoal, and clears
    the temporary.

    [H] names the Iris hypothesis holding a [structR] or [primR] from
    which [reference_to] can be observed.

    Replaces:
<<
      iDestruct (observe (reference_to _ _) with H) as "#_obs";
      iSplitR; [iExact "_obs" |]; iClear "_obs".
>>
*)
Ltac wp_observe_ref H :=
  iDestruct (observe (reference_to _ _) with H) as "#_obs";
  iSplitR; [iExact "_obs" |]; iClear "_obs".

(* ================================================================= *)
(** ** Layer 2: Composite Tactics *)
(* ================================================================= *)

(** Read a local variable via l2r cast.

    [H] is a string naming the Iris hypothesis holding the [tptsto_fuzzyR]
    for the local variable. [v] is the value stored in it (e.g. [Vint k]
    or [Vptr n]).

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

(** Destroy a local variable of primitive type.

    [H] is the hypothesis name holding [tptsto_fuzzyR] for the local.

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

(** Provide [initializedR] evidence from [primR].

    [H] names the Iris hypothesis holding [(p ,, f) |-> primR ty q v]
    (e.g. [intR q kn_tc]). [v] is the value (e.g. [Vint kn_tc]).

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

(** Structural prefix for [ptr->field] access.

    Handles the l2r cast -> member access -> arrow dereference prefix that
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

(** Observe + offset + provide value for a struct field access.

    After reading the parent pointer, this handles the [reference_to] observe
    from the struct, the [read_decl] + field offset conversion, and the value
    provision.  Composes [wp_observe_ref] twice: once for the struct identity
    and once for the field after offset conversion.

    [H_struct] is the hypothesis for the struct identity ([structR]).
    [H_field] is the hypothesis for the field ([primR] / [ptrR]).
    [v] is the expected value (e.g. [Vptr lp]).
*)
Ltac wp_struct_field H_struct H_field v :=
  wp_observe_ref H_struct;
  rewrite /read_decl /=;
  wp_offset H_field;
  wp_observe_ref H_field;
  wp_provide_value H_field v.

(** L-value target of [local = rhs].

    After the RHS of an assignment is evaluated, this handles the l-value
    target: resolves the local variable, provides [reference_to] evidence
    (via [wp_observe_ref]), and transfers ownership (old value -> [anyR]).

    [H_local] names the Iris hypothesis holding [tptsto_fuzzyR] for the
    local variable being assigned to.

    After the tactic, [iIntros "H_new"] binds the fresh [tptstoR] for
    the updated local.
*)
Ltac wp_assign_local H_local :=
  iApply wp_lval_var;
  rewrite /read_decl /_local /=;
  wp_observe_ref H_local;
  iSplitL H_local; [wp_finish_anyR |].

(** Prove [eval_binop] for an integer binary operation.

    Generalizes [wp_eval_int_lt] by parameterizing the eval lemma.
    [H_hty] names the persistent Iris hypothesis holding
    [has_type_or_undef (Vint _) Tint]. [eval_lemma] is the evaluation
    lemma to apply (e.g. [eval_lt], [eval_le], etc.).

    Future aliases (e.g. [wp_eval_int_le]) are one-liners.
*)
Ltac wp_eval_int_binop H_hty eval_lemma :=
  iSplitR; [| done];
  rewrite /eval_binop;
  iLeft;
  iRevert H_hty;
  rewrite has_type_or_undef_unfold;
  iIntros "[_htmp | %_habs]"; [| discriminate];
  iDestruct (has_type_has_type_prop with "_htmp") as "%_htp";
  iPureIntro;
  eapply eval_lemma; [solve [typeclasses eauto] | done | assumption | assumption].

(** Prove [eval_binop] for integer [<]. Alias for [wp_eval_int_binop]. *)
Ltac wp_eval_int_lt H_hty := wp_eval_int_binop H_hty eval_lt.

(** Prove [nullptr != nullptr] evaluates to false (Leaf/null case).

    Used when the current pointer is nullptr (e.g. at a Leaf node)
    and we need to show the loop condition [curr != nullptr] is false.

    [tu] is the translation unit (e.g. [source]).
    [cls] is the class name (e.g. [_Node]).

    Replaces:
<<
      iPoseProof valid_ptr_nullptr as "Hvn";
      iPoseProof (eval_ptr_self_eq tu cls nullptr with "Hvn") as "Heq";
      iPoseProof (eval_ptr_neq tu cls nullptr nullptr true with "Heq")
        as "[Himpure Htrue]";
      rewrite /eval_binop;
      iFrame "Htrue"; iRight; iExact "Himpure".
>>
*)
Ltac wp_eval_ptr_neq_null tu cls :=
  iPoseProof valid_ptr_nullptr as "_pvn";
  iPoseProof (eval_ptr_self_eq tu cls nullptr with "_pvn") as "_peq";
  iPoseProof (eval_ptr_neq tu cls nullptr nullptr true with "_peq")
    as "[_pimp _ptrue]";
  rewrite /eval_binop;
  iFrame "_ptrue"; iRight; iExact "_pimp".

(** Prove [cv != nullptr] evaluates to true (Node/nonnull case).

    Used when the current pointer is non-null (e.g. at a Node) and we
    need to show the loop condition [curr != nullptr] is true.

    [tu] is the translation unit (e.g. [source]).
    [cls] is the class name (e.g. [_Node]).
    [H_valid] names the persistent Iris hypothesis holding [valid_ptr cv].

    Uses [match goal] to find the [?p <> nullptr] hypothesis automatically.

    Replaces:
<<
      match goal with Hne : cv <> nullptr |- _ =>
        iPoseProof (eval_ptr_nullptr_eq_l tu
          (fun _ : is_Some (ptr_vaddr cv) =>
             bool_decide_eq_false_2 (cv = nullptr) Hne)
          with H_valid) as "Heq"
      end;
      iPoseProof (eval_ptr_neq tu cls cv nullptr false with "Heq")
        as "[Himpure Htrue]";
      rewrite /eval_binop;
      iFrame "Htrue"; iRight; iExact "Himpure".
>>
*)
Ltac wp_eval_ptr_neq_nonnull tu cls H_valid :=
  match goal with Hne : ?p <> nullptr |- _ =>
    iPoseProof (eval_ptr_nullptr_eq_l tu
      (fun _ : is_Some (ptr_vaddr p) =>
         bool_decide_eq_false_2 (p = nullptr) Hne)
      with H_valid) as "_peq";
    iPoseProof (eval_ptr_neq tu cls p nullptr false with "_peq")
      as "[_pimp _ptrue]"
  end;
  rewrite /eval_binop;
  iFrame "_ptrue"; iRight; iExact "_pimp".

(** Deduplicate [nd_seq] orderings for binops.

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
*)
Ltac wp_binop tu eval_a eval_b kont :=
  iApply (wp_operand_binop tu);
  rewrite /nd_seq;
  iSplit; [ eval_a; eval_b; kont | eval_b; eval_a; kont ].

(* ================================================================= *)
(** ** Layer 3: Meta-Tactics *)
(* ================================================================= *)

(** [wp_step] performs one mechanical wp proof step by trying rules in
    priority order. [wp_auto] repeats it until stuck.

    Design principle: [wp_auto] handles ALL mechanical/syntactic steps
    (modality stripping, AST-driven wp rules, definitional unfolding).
    The user provides ONLY semantic steps (loop invariants, case splits,
    eval_binop proofs, resource framing, hypothesis destructuring).

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

(** Expression-level AST dispatcher (experimental).

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
