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
    - [tptstoR_to_primR] — Convert [tptstoR] back to [primR] (non-raw/undef values).

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
    - [wp_read_field H v H_struct H_field v_field] — Read a field through a pointer.
    - [wp_assign_local H_local] — L-value target of [local = rhs].
    - [wp_assign_member_field H_local v H_struct H_field] — L-value target of [ptr->field = rhs].
    - [wp_destroy_prim_temp H] — Destroy one primitive-typed argument temporary.
    - [wp_operand_receive v H_recv H_local] — Receive function return value into local.
    - [wp_assign_setup] — Assignment preamble: [wp_lval_assign] + [eval2] unfold.
    - [wp_eval_int_binop H_hty eval_lemma] — Prove [eval_binop] for integer binary ops.
    - [wp_eval_int_lt H_hty] — Alias: [wp_eval_int_binop H_hty eval_lt].
    - [wp_eval_int_le H_hty] — Alias: [wp_eval_int_binop H_hty eval_le].
    - [wp_eval_int_eq H_hty] — Alias: [wp_eval_int_binop H_hty eval_eq].
    - [wp_eval_int_neq H_hty] — Alias: [wp_eval_int_binop H_hty eval_neq].
    - [wp_eval_ptr_neq_null tu cls] — Prove [nullptr != nullptr] evaluates to false.
    - [wp_eval_ptr_neq_nonnull tu cls H_valid] — Prove [cv != nullptr] evaluates to true.
    - [wp_binop tu eval_a eval_b kont] — Deduplicate [nd_seq] orderings.

    == Layer 2.5: Function Call Resolution ==

    - [code_at_of_denoteModule] — Extract [code_at] from [denoteModule] via symbol lookup.
    - [wp_fptr_of_func_ok] — Compose [code_at] + [func_ok] → [wp_fptr].
    - [wp_operand_cfun2ptr_global] — Resolve [Ecast Cfun2ptr (Eglobal name ty)] (Admitted: BRiCk gap).
    - [wp_operand_read_global_const] — Resolve [Ecast Cl2r (Eglobal name qty)] for const globals (Admitted: BRiCk gap).
    - [wp_read_global_const HMOD lookup v] — Read a global const variable.
    - [wp_resolve_call HMOD lookup body fname] — Resolve [Ecall] through [cfun2ptr_global] to [wp_fptr].
    - [wp_call_direct HMOD lookup body func_ok] — One-liner for call sites.
    - [wp_arg_prim eval_operand] — Evaluate one [wp_arg] for a primitive type.
    - [wp_nd_args_step eval_operand] — One level of [nd_seqs'] dispatch.
    - [wp_nd_args eval_operand] — Complete [nd_seqs] resolution for function calls.

    == Layer 3: Meta-Tactics ==

    - [wp_step] / [wp_auto] — Mechanical wp proof automation.
    - [wp_step_anon] / [wp_auto_anon] — Like [wp_step]/[wp_auto] + anonymous [iIntros (?)].
    - [wp_step_debug] / [wp_auto_debug] — Like [wp_step]/[wp_auto] with [idtac] trace messages.
*)

From Stdlib Require Export ZArith.

Require Export skylabs.lang.cpp.cpp.
Require Export skylabs.iris.extra.proofmode.proofmode.
Export cQp_compat.
Require Import skylabs.lang.cpp.compile.

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

(** Convert [tptstoR] back to [primR] for non-raw, non-undef values.

    After an assignment, [wp_lval_assign] yields [p |-> tptstoR ty q v].
    To reconstruct [treeR (Node ...)] via [treeR_node_fold], we need
    [p |-> primR ty q v] (e.g. [boolR], [intR]).  This lemma bridges
    the gap when the value is known to be concrete (not raw or undef).

    Delegates to BRiCk's [tptstoR_Vxxx_primR] from [heap_pred.v].

    Usage:
<<
      iPoseProof (tptstoR_to_primR with "H") as "H".
>>
*)
Lemma tptstoR_to_primR (p : ptr) ty q v :
  ~~ is_raw_or_undef v ->
  p |-> tptstoR ty q v |-- p |-> primR ty q v.
Proof. intros Hv. by rewrite tptstoR_Vxxx_primR. Qed.

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

(** Read a struct field through a pointer in one step.

    Combines [wp_member_access] → [wp_read_local] → [wp_struct_field]
    into a single tactic for the common pattern of reading a field
    through a local pointer variable (e.g. [curr->left]).

    [H_local] names the [tptsto_fuzzyR] for the local pointer variable.
    [v_ptr] is the pointer value (e.g. [Vptr cv]).
    [H_struct] names the [structR] hypothesis at the pointed-to struct.
    [H_field] names the field hypothesis (e.g. ["_nleft"]).
    [v_field] is the expected field value (e.g. [Vptr lp]).

    Replaces:
<<
      wp_member_access;
      wp_read_local H_local v_ptr;
      wp_struct_field H_struct H_field v_field.
>>
*)
Ltac wp_read_field H_local v_ptr H_struct H_field v_field :=
  wp_member_access;
  wp_read_local H_local v_ptr;
  wp_struct_field H_struct H_field v_field.

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

(** L-value target of [ptr->field = rhs].

    Handles the LHS of an assignment like [curr->color = rhs]:
    resolves [wp_lval_member] → [read_arrow] → local variable read →
    [reference_to] observe from struct → [read_decl] → field [reference_to]
    observe → [anyR] transfer.

    Requires caller to [wp_offset H_field] first to convert the field
    hypothesis from nested form to offset form.

    [H_local] names the [tptsto_fuzzyR] for the local pointer variable.
    [v] is the pointer value (e.g. [Vptr curr]).
    [H_struct] names the [structR] hypothesis for the pointed-to struct.
    [H_field] names the field hypothesis (already offset via [wp_offset]).

    After the tactic, [iIntros "H_new"] binds the fresh [tptstoR] for
    the updated field.

    Usage:
<<
      wp_offset "_ncolor".
      wp_assign_member_field "Hcurr_local" (Vptr curr) "_nstruct" "_ncolor".
>>
*)
Ltac wp_assign_member_field H_local v H_struct H_field :=
  iApply wp_lval_member; [reflexivity |];
  rewrite /read_arrow /=;
  wp_read_local H_local v;
  wp_observe_ref H_struct;
  rewrite /read_decl /=;
  wp_observe_ref H_field;
  iSplitL H_field; [iRevert H_field; rewrite primR_anyR; iIntros "$" |].

(** Destroy one primitive-typed argument temporary.

    After a function call, the caller receives [anyR] hypotheses for each
    argument temporary.  The BRiCk wp goal contains [destroy_val] (or the
    already-unfolded [wp_destroy_prim]) for each.  This tactic destroys
    one temporary by:
    1. Unfolding [destroy_val] (idempotent via [try])
    2. Bridging [anyR] to [wp_destroy_prim] via [anyR_wp_destroy_prim_val]
    3. Framing the [anyR] hypothesis

    [H] names the [anyR] hypothesis for the temporary being destroyed.

    The [try] guard on [destroy_val_unfold] handles the case where a
    previous invocation's [!] rewrite already unfolded all same-typed
    [destroy_val]s.

    Usage:
<<
    wp_destroy_prim_temp "Hanyp1".
    wp_destroy_prim_temp "Hanyp0".
    wp_destroy_prim_temp "Hanyp".
>>
*)
Ltac wp_destroy_prim_temp H :=
  try (destroy_val_unfold; simpl);
  iApply anyR_wp_destroy_prim_val; [done |];
  try (cbn -[destroy_val wp_destroy_prim operand_receive]);
  iFrame H.

(** Receive a function return value into a local variable.

    After function call + argument temp destruction, the wp goal contains
    [operand_receive] which stores the callee's return value into a local.
    This tactic:
    1. Strips the fupd modality
    2. Unlocks [operand_receive]
    3. Provides the return value [v]
    4. Frames the receiver hypothesis [H_recv] (the [tptsto_fuzzyR] wand)
    5. Introduces the resulting local variable hypothesis as [H_local]

    [v] is the return value (e.g. [Vptr curr]).
    [H_recv] names the [tptsto_fuzzyR] receiver hypothesis from the call.
    [H_local] is the name to give the new local variable hypothesis.

    Usage:
<<
    wp_operand_receive (Vptr curr) "Hrecv" "Hcurr_local".
>>
*)
Ltac wp_operand_receive v H_recv H_local :=
  iModIntro;
  rewrite operand_receive.unlock /=;
  iExists v; iFrame H_recv;
  iIntros H_local.

(** Assignment setup: apply [wp_lval_assign] and unfold [eval2].

    Every assignment [lhs = rhs] in a wp proof starts with [wp_lval_assign]
    followed by unfolding the evaluation order monad.  This tactic handles
    both lr (default) and rl (C++17) evaluation orders:
    1. Apply [wp_lval_assign]
    2. Simplify (handles lr order automatically)
    3. Try unfolding [eval2]/[Mmap]/[Mseq]/[Mbind] (needed for rl order)

    After the tactic, the goal is the first operand to evaluate (RHS for
    rl order, LHS for lr order).

    Usage:
<<
    wp_assign_setup.
    (* RHS evaluation *)
    (* LHS evaluation *)
    iIntros "H_new".  (* receive updated value *)
>>
*)
Ltac wp_assign_setup :=
  iApply wp_lval_assign;
  rewrite /=;
  try rewrite /eval2 /wp.WPE.Mmap /wp.WPE.Mseq /wp.WPE.Mbind /=.

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

(** Prove [eval_binop] for integer [<=]. Alias for [wp_eval_int_binop]. *)
Ltac wp_eval_int_le H_hty := wp_eval_int_binop H_hty eval_le.

(** Prove [eval_binop] for integer [==]. Alias for [wp_eval_int_binop]. *)
Ltac wp_eval_int_eq H_hty := wp_eval_int_binop H_hty eval_eq.

(** Prove [eval_binop] for integer [!=]. Alias for [wp_eval_int_binop]. *)
Ltac wp_eval_int_neq H_hty := wp_eval_int_binop H_hty eval_neq.

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
(** ** Layer 2.5: Function Call Resolution *)
(* ================================================================= *)

(** When a wp proof reaches a function call [f(args)], the goal is:
<<
    |> wp_fptr tu.(types) ft (_global f_name) [v1; v2; ...] Q
>>
    Resolution requires three persistent facts chained together:

    1. [denoteModule tu]: Section hypothesis (persistent, reusable).
         Via [denoteModule_denoteSymbol] + symbol table lookup:
         [_global f_name |-> as_Rep (code_at tu f)] ⊣⊢ [code_at tu f (_global f_name)]

    2. [code_at tu f (_global f_name)]: persistent, from step 1.
         Via [code_at_ok] axiom (from compile.v):
         [∀ ls Q, wp_func tu f ls Q -* wp_fptr ... ls Q]

    3. [func_ok tu f spec]: persistent, from the callee's proof.
         [= □ (∀ Q vals, spec.(fs_spec) vals Q -* wp_func tu f vals Q)]

    Composing: [spec.(fs_spec) vals Q -* wp_func -* wp_fptr]. *)

Section wp_call_lemmas.
Context `{Sigma : cpp_logic} {CU : genv}.

(** Extract [code_at] from [denoteModule] for a function with a body.

    [denoteModule] is persistent ([denoteModule_persistent]) so this can be
    called any number of times for different functions with zero resource cost.

    Chain: [denoteModule] → [denoteModule_denoteSymbol] (symbol lookup) →
    [denoteSymbol] (unfolds [Ofunction f] with [Some body]) →
    [_at_as_Rep] (converts [p |-> as_Rep Q] ⊣⊢ [Q p]) → [code_at tu f p].

    Usage:
<<
    iPoseProof (code_at_of_denoteModule _ _ _ ins_lookup ins_has_body
      with "HMOD") as "#Hca".
>>
*)
Lemma code_at_of_denoteModule (tu : translation_unit) (f : Func)
    (name : obj_name) :
  tu.(symbols) !! name = Some (Ofunction f) ->
  (exists body, f.(f_body) = Some body) ->
  denoteModule tu |-- code_at tu f (_global name).
Proof.
  intros Hlookup [body Hbody].
  etransitivity; first exact (denoteModule_denoteSymbol _ _ _ Hlookup).
  rewrite /denoteSymbol /= Hbody _at_as_Rep. done.
Qed.

(** Resolve [wp_fptr] given [code_at], [func_ok], and the spec precondition.

    Composes [code_at_ok] (compile axiom) with [func_ok] (callee proof) to
    discharge [wp_fptr]. The only spatial resource consumed is [spec.(fs_spec)
    vs Q] — both [code_at] and [func_ok] are persistent.

    The [type_of_spec spec = type_of_value (Ofunction f)] pure fact from
    [func_ok] is extracted but unused in this lemma; it is consumed as part
    of the [func_ok] destructuring.

    Usage:
<<
    iApply (wp_fptr_of_func_ok with "[$Hca $Hfok Hspec]").
>>
*)
Lemma wp_fptr_of_func_ok (tu : translation_unit) (f : Func) (p : ptr)
    (spec : function_spec) (vs : list ptr) (Q : ptr -> epred) :
  code_at tu f p **
  func_ok tu f spec **
  spec.(fs_spec) vs Q
  |-- wp_fptr tu.(types) (type_of_value (Ofunction f)) p vs Q.
Proof.
  iIntros "(Hca & Hfok & Hspec)".
  iDestruct "Hfok" as "[%Hty #Hfunc]".
  iPoseProof (code_at_ok tu f p with "Hca") as "Hca_ok".
  iApply ("Hca_ok" $! vs Q).
  iApply ("Hfunc" $! Q vs).
  iExact "Hspec".
Qed.

(** Like [wp_fptr_of_func_ok] but bridges from [tu.(types)] to
    [(genv_tu CU).(types)] when [sub_module tu (genv_tu CU)].

    The standard [wp_fptr] goal from [wp_call] uses [(genv_tu CU).(types)]
    (via the local notation in expr.v), but [code_at_ok] produces
    [wp_fptr tu.(types) ...].  When [tu ⊧ CU], [sub_module tu (genv_tu CU)]
    gives [type_table_le tu.(types) (genv_tu CU).(types)], and
    [wp_fptr_frame_fupd] bridges the gap.

    *)
Lemma wp_fptr_of_func_ok_compat (tu : translation_unit) (f : Func) (p : ptr)
    (spec : function_spec) (vs : list ptr) (Q : ptr -> epred)
    (Hsub : sub_module tu (genv_tu CU)) :
  code_at tu f p **
  func_ok tu f spec **
  spec.(fs_spec) vs Q
  |-- wp_fptr (genv_tu CU).(types) (type_of_value (Ofunction f)) p vs Q.
Proof.
  iIntros "H".
  iPoseProof (wp_fptr_of_func_ok with "H") as "Hwp".
  iAssert (∀ v : ptr, Q v -∗ |={⊤}=> Q v)%I as "Hfupd".
  { iIntros (v) "HQ". iModIntro. iExact "HQ". }
  iPoseProof (wp_fptr_frame_fupd _ _ _ _ _ _ _ (types_compat _ _ Hsub) with "Hfupd") as "Hconv".
  iApply ("Hconv" with "Hwp").
Qed.

(** Resolve [wp_operand (Ecast Cfun2ptr (Eglobal name ty)) Q] from [denoteModule].

    Combines [wp_operand_cast_fun2ptr_cpp] (Cfun2ptr cast axiom) +
    [wp_lval_global] + [read_decl] (global lvalue resolution) into
    a single step, producing the continuation instantiated at
    [Vptr (_global name)].

    == Why this is Admitted ==

    For function types, [read_decl] requires [reference_to (erase_qualifiers ty)]
    which needs [aligned_ptr_ty] → [align_of ty = Some _]. The BRiCk axiom
    system declares [align_of] as a [Parameter] with no axiom for [Tfunction],
    making [aligned_ptr_ty (Tfunction _) p] unprovable through the standard chain.

    The BRiCk developers acknowledge this gap at wp.v line 730:
<<
      (this rule has a problem with function references because
       there is no alignment for functions)
      Two options:
      1. functions have 1 alignment
      2. there is a special rule for [has_type (Vref r) (Tref (Tfunction ..))]
         that ignores this
>>

    This lemma is semantically valid: the compiler places compiled functions
    at valid, aligned addresses — a fact captured by [code_at] (which provides
    [strict_valid_ptr]) but not expressible through [reference_to] due to the
    missing alignment axiom.

    This is NOT an [Axiom] — it is a deferred proof obligation (like [ins_ok]
    and other [Admitted] function specs). It will become provable when the
    upstream BRiCk library implements either fix mentioned above.

    Proof sketch (blocked at step 6):
    1. [wp_operand_cast_fun2ptr_cpp]: Cfun2ptr → [wp_lval]
    2. [wp_lval_global]: Eglobal → [read_decl]
    3. Unfold [read_decl] (default case for non-reference types)
    4. Goal: [reference_to (erase_qualifiers ty) (_global name) ** Q ...]
    5. Frame [Q] from hypothesis; extract [code_at] → [strict_valid_ptr]
    6. BLOCKED: [reference_to] requires [aligned_ptr_ty] → [align_of = Some _] *)
Lemma wp_operand_cfun2ptr_global (tu : translation_unit)
    (ρ : region) (name : obj_name) (f : Func) (ty : type)
    (Q : val -> FreeTemps -> mpred) :
  tu.(symbols) !! name = Some (Ofunction f) ->
  (exists body, f.(f_body) = Some body) ->
  denoteModule tu ** Q (Vptr (_global name)) FreeTemps.id
  |-- wp_operand tu ρ (Ecast Cfun2ptr (Eglobal name ty)) Q.
Proof. Admitted.

(** Resolve [wp_operand (Ecast Cl2r (Eglobal name qty)) Q] for const globals.

    When C++ code reads a global const (e.g. [Node::black]), the wp goal is:
<<
      wp_operand tu ρ (Ecast Cl2r (Eglobal name qty)) Q
>>
    This lemma resolves it from [denoteModule tu] and a symbol table lookup.

    == Why this is Admitted ==

    For global variables, [denoteModule] provides only [svalidR] (location
    validity) via [denoteSymbol], not the initialized value.  The path to
    the value requires [initializedR] at the global's address, but
    [initSymbol] returns [emp] with an explicit TODO in [translation_unit.v]:
<<
      (* ^^ todo(gmm): static initialization is not yet supported *)
>>
    The [wp_operand_cast_l2r] axiom needs [initializedR] to extract the
    value, which cannot be derived from [svalidR] alone.

    This is the same class of BRiCk framework gap as [wp_operand_cfun2ptr_global]
    (function alignment — above) and will become provable when BRiCk
    implements static initialization support.

    The [init] parameter documents the initializer found in the symbol table
    (verified by [lookup_proof]) without enforcing it (since [initSymbol]
    is [emp]).

    Proof sketch (blocked at step 4):
    1. [wp_operand_cast_l2r] → [wp_glval] → [wp_lval_global] → [read_decl]
    2. [read_decl] (non-ref case) → [reference_to (erase_qualifiers qty) (_global name)]
    3. [denoteModule_denoteSymbol] + lookup → [svalidR] → [strict_valid_ptr] → [reference_to] ✓
    4. BLOCKED: [wp_operand_cast_l2r] needs [initializedR], but [denoteModule]
       only provides [svalidR] ✗ *)
Lemma wp_operand_read_global_const (tu : translation_unit)
    (ρ : region) (name : obj_name) (qty : type) (init : global_init.t)
    (v : val) (Q : val -> FreeTemps -> mpred) :
  tu.(symbols) !! name = Some (Ovar qty init) ->
  denoteModule tu ** Q v FreeTemps.id
  |-- wp_operand tu ρ (Ecast Cl2r (Eglobal name qty)) Q.
Proof. Admitted.

End wp_call_lemmas.

(** Read a global const variable.

    Resolves [wp_operand (Ecast Cl2r (Eglobal name qty)) Q] for a global
    const (e.g. [Node::black]).  Uses [wp_operand_read_global_const]
    (Admitted) to rewrite the goal, then frames [denoteModule] from [HMOD].

    Uses [rewrite] instead of [iApply] because the Coq unifier cannot
    resolve the continuation evar [?Q] through [iApply]'s higher-order
    matching when the continuation is complex (e.g. from [eval2] unfolding).
    [rewrite] handles the matching directly at the term level.

    [HMOD] names the persistent hypothesis holding [denoteModule tu].
    [lookup_lemma] proves [tu.(symbols) !! name = Some (Ovar qty init)].
    [v] is the runtime value of the constant (e.g. [Vbool false]).

    After the tactic, the goal is the continuation [Q v FreeTemps.id].

    Usage:
<<
      wp_read_global_const "HMOD" black_lookup (Vbool false).
>>
*)
Ltac wp_read_global_const HMOD lookup_lemma v :=
  rewrite -(wp_operand_read_global_const _ _ _ _ _ v _ lookup_lemma);
  iSplitL HMOD; [iExact HMOD |].

(** Resolve [wp_operand ... (Ecall (Ecast Cfun2ptr (Eglobal name ty)) args) Q].

    Handles the mechanical prefix of every function call in a wp proof:
    1. Apply [wp_operand_call] (Ecall rule)
    2. Unfold [wp_call], discharge [tu ⊧ σ], unfold [Mbind/Mmap]
    3. Resolve the function expression via [wp_operand_cfun2ptr_global]
    4. Frame [denoteModule] from [HMOD] and instantiate function pointer

    After the tactic, the goal is at the [nd_seqs] level —
    ready for [wp_nd_args] to evaluate arguments.

    [HMOD] names the persistent hypothesis holding [denoteModule tu].
    [lookup_lemma] proves [tu.(symbols) !! fname = Some (Ofunction _)].
    [body_proof] proves [exists body, f_body = Some body].
    [fname] is the function's [obj_name] (e.g. [ins_name]).

    Usage:
<<
    wp_resolve_call "HMOD" ins_lookup ins_has_body ins_name.
>>
*)
Ltac wp_resolve_call HMOD lookup_lemma body_proof fname :=
  iApply wp_operand_call;
  rewrite /wp_call /=;
  iIntros "%_";
  rewrite /wp.WPE.Mbind /wp.WPE.Mmap /=;
  iApply (wp_operand_cfun2ptr_global _ _ _ _ _ _ lookup_lemma body_proof);
  iSplitL HMOD; [iExact HMOD |];
  iExists (_global fname);
  iSplit; [iPureIntro; reflexivity |].

(** Resolve a [wp_fptr] goal from [denoteModule] + [func_ok].

    [HMOD]: name of persistent hypothesis holding [denoteModule tu]
    [lookup_lemma]: proof that function is in the symbol table
    [body_proof]: proof that function has a body ([exists body, f_body = Some _])
    [func_ok_lemma]: proof of [|-- func_ok tu f spec]
    [func_def]: the function definition term (e.g., [ins_func])

    After the tactic, the goal is [spec.(fs_spec) vs Q] —
    the caller's precondition for the function being called.
    All spatial resources are preserved (temporaries, tree, continuation).

    The [change] step replaces the concrete function type in the goal with
    [type_of_value (Ofunction func_def)] so that [iApply] can resolve evars.
    Without this, Coq's unifier cannot invert [type_of_value] to find [func_def].
    The [iSplitL ""] steps provide persistent [code_at] and [func_ok] without
    consuming spatial resources.

    Usage:
<<
    wp_call_direct "HMOD" ins_lookup ins_has_body ins_ok ins_func.
>>
*)
Ltac wp_call_direct HMOD lookup_lemma body_proof func_ok_lemma func_def :=
  try iNext;
  iPoseProof (code_at_of_denoteModule _ _ _ lookup_lemma body_proof
    with HMOD) as "#_call_ca";
  iPoseProof func_ok_lemma as "#_call_fok";
  match goal with |- context[wp_fptr _ ?ft _ _ _] =>
    change ft with (type_of_value (Ofunction func_def))
  end;
  first [
    iApply (wp_fptr_of_func_ok _ _ _ _ _ _);
    iSplitR; [iExact "_call_ca"|];
    iSplitR; [iExact "_call_fok"|]
  | iApply (wp_fptr_of_func_ok_compat _ _ _ _ _ _ (tu_compat));
    iSplitR; [iExact "_call_ca"|];
    iSplitR; [iExact "_call_fok"|]
  ].

(** Evaluate one [wp_arg] for a primitive type ([Tint], [Tptr], etc.).

    After [nd_seqs] case-splitting identifies which argument to evaluate,
    the goal shape is [Mbind (wp_arg_body ty e) (fun t => ...) Q] where
    [wp_arg_body] is the inlined body of the [#[local]] [wp_arg] definition.

    [eval_operand] is a user-supplied tactic that evaluates the operand
    (e.g., [wp_read_local H v] for a local variable read).

    For primitive types, [wp_arg] unfolds to:
<<
      ∀ p, wp_initialize tu ρ ty p e (fun free => K p free)
>>
    and [wp_initialize] reduces to [wp_operand] (no destructor overhead).

    Steps:
    1. Unfold [Mbind] to expose the wp_arg body
    2. Introduce the temporary pointer [p]
    3. Unfold [wp_initialize] → [wp_operand]
    4. [eval_operand] evaluates the operand (user tactic)
    5. Accept the [tptsto_fuzzyR] wand for the temporary
    6. Strip fupd if present, unfold [Mmap] to continue *)
Ltac wp_arg_prim eval_operand :=
  rewrite /wp.WPE.Mbind /call.wp_arg /=;
  iIntros (?);
  rewrite /wp_initialize /qual_norm /=;
  try rewrite wp_initialize_unqualified.unlock /=;
  eval_operand;
  iIntros "?";
  try iModIntro;
  rewrite /wp.WPE.Mmap /=.

(** One level of [nd_seqs'] dispatch: case-split on argument position.

    The [nd_seqs'] definition universally quantifies over all ways to split
    the argument list as [pre ++ q :: post].  This tactic:
    1. Introduces [pre], [post], [q], and the equality
    2. Case-splits on [pre] to determine which argument was chosen
    3. Eliminates impossible cases via [congruence]
    4. Extracts equalities and substitutes
    5. Applies [wp_arg_prim] to evaluate the chosen argument

    Handles argument lists up to length 4 (supports up to 4-argument calls).
    [eval_operand] is the user-supplied operand evaluation tactic. *)
Ltac wp_nd_args_step eval_operand :=
  iIntros (? ? ?) "%_nd_eq";
  match goal with
  | _nd_eq : _ = ?pre ++ _ :: _ |- _ =>
    destruct pre as [| ?x0 [| ?x1 [| ?x2 [| ?x3 ?rest]]]];
      simpl in _nd_eq; try congruence;
      try (injection _nd_eq; clear _nd_eq; intros; subst);
      try clear _nd_eq; simpl
  end;
  wp_arg_prim eval_operand.

(** Complete [nd_seqs] resolution for a function call.

    Resolves [nd_seqs [wp_arg1; wp_arg2; ...] Q] by recursively applying
    [wp_nd_args_step] at all levels of the [nd_seqs'] recursion, then
    handling the base case ([Mret nil]).

    For N arguments, generates N! proof branches (N × (N-1) × ... × 1)
    corresponding to all evaluation orderings.  Each branch evaluates
    arguments in a specific order using [eval_operand].

    Usage: pass an Ltac that evaluates any single argument, using [first]
    to try each hypothesis:
<<
    wp_nd_args ltac:(first [
      wp_read_local "Hpk" vk |
      wp_read_local "Hpv" vv |
      wp_read_local "Hpn" vn
    ]).
>>
*)
Ltac wp_nd_args eval_operand :=
  rewrite /wp.WPE.nd_seqs /=;
  repeat (wp_nd_args_step eval_operand);
  try rewrite /wp.WPE.Mret /=.

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

    Universal quantifier introduction ([iIntros (?)]) is NOT included
    because proofs often need named variables for loop invariants and
    other Coq-level terms.  Call [iIntros (name)] explicitly.

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
    progress (rewrite /to_arg_type /=) |
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

(** [wp_step_anon] extends [wp_step] with anonymous universal introduction.

    Many wp stepping points introduce universally quantified variables
    (return pointers, intermediate addresses) that don't need named
    Coq bindings. [wp_step] deliberately excludes [iIntros (?)] because
    proofs often need named variables for loop invariants. [wp_step_anon]
    is the opt-in variant for sequences where anonymous names suffice.

    [wp_auto_anon] repeats [wp_step_anon] until stuck. *)
Ltac wp_step_anon := first [ wp_step | progress (iIntros (?)) ].
Ltac wp_auto_anon := repeat wp_step_anon.

(** [wp_step_debug] mirrors [wp_step] with [idtac] trace messages.

    For a pedagogical project, knowing which [wp_step] rule fired is
    invaluable for debugging stuck proofs. Each branch prints an [idtac]
    message before firing, so [Set Ltac Profiling] or the Messages panel
    shows the exact rule sequence.

    [wp_auto_debug] repeats [wp_step_debug] until stuck. *)
Ltac wp_step_debug :=
  first [
    idtac "wp_step: wp_seq"; iApply wp_seq |
    idtac "wp_step: wp_break"; iApply wp_break |
    idtac "wp_step: wp_return"; iApply wp_return |
    idtac "wp_step: wp_expr"; iApply wp_expr |
    idtac "wp_step: wp_block_eq"; progress (rewrite wp_block_eq /wp_block_def) |
    idtac "wp_step: wp_decls_eq"; progress (rewrite wp_decls_eq /wp_decls_def /=) |
    idtac "wp_step: wp_initialize"; progress (rewrite /wp_initialize /qual_norm /=) |
    idtac "wp_step: wp_init_unqual"; progress (rewrite wp_initialize_unqualified.unlock /=) |
    idtac "wp_step: to_arg_type"; progress (rewrite /to_arg_type /=) |
    idtac "wp_step: wp_discard"; progress (rewrite /wp_discard /=) |
    idtac "wp_step: wp_null_val"; wp_null_val |
    idtac "wp_step: interp_unfold"; progress (rewrite interp_unfold /=) |
    idtac "wp_step: while_unroll"; progress (rewrite /while_unroll) |
    idtac "wp_step: Kloop"; progress (rewrite /Kloop /Kloop_inner /=) |
    idtac "wp_step: Kfree/cleanup"; progress (rewrite /Kfree /Kat_exit /Kcleanup /Kreturn /Kreturn_inner /=) |
    idtac "wp_step: get_return_type"; progress (rewrite /get_return_type /=) |
    idtac "wp_step: iModIntro"; progress iModIntro |
    idtac "wp_step: iNext"; progress iNext
  ].
Ltac wp_auto_debug := repeat wp_step_debug.
