(** * Two BRiCk Framework Gaps: Function Alignment & Static Initialization

    NOTE: This file is a documentation artifact, not part of the proof build
    (it is intentionally excluded from the Makefile and _CoqProject). It records
    two framework-level gaps encountered during the insert proof, stated as
    self-contained [Admitted] lemmas for discussion with BRiCk maintainers.

    We are verifying a C++ red-black tree against its cpp2v-generated AST
    using BRiCk (Coq + Iris separation logic).  During proof development we
    encountered two lemmas that appear semantically valid but are blocked by
    missing framework support.  We'd appreciate guidance on whether there is
    a workaround we're missing, or whether these are known gaps with planned
    fixes.

    The lemma statements below are self-contained — they depend only on
    standard BRiCk imports, no project-specific definitions.
*)

From Stdlib Require Import ZArith.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.lang.cpp.compile.

Section gaps.
Context `{Sigma : cpp_logic} {CU : genv}.

(** ** Gap 1: [Cfun2ptr] cast for global functions

    When C++ code calls a function [f(args)], the wp goal for the callee
    expression [f] is:
<<
    wp_operand tu ρ (Ecast Cfun2ptr (Eglobal name ty)) Q
>>
    We can reduce this via [wp_operand_cast_fun2ptr_cpp] → [wp_lval_global]
    → [read_decl], at which point the goal requires:
<<
    reference_to (erase_qualifiers ty) (_global name)
>>
    For function types, [reference_to] needs [aligned_ptr_ty], which needs
    [align_of ty = Some _].  But [align_of] (a [Parameter] in BRiCk) has
    no axiom for [Tfunction], so the chain is blocked.

    We noticed the comment at [wp.v] (around line 730):

<<
    (this rule has a problem with function references because
     there is no alignment for functions)
    Two options:
    1. functions have 1 alignment
    2. there is a special rule for [has_type (Vref r) (Tref (Tfunction ..))]
       that ignores this
>>

    Question: Has either fix been implemented (perhaps in a development
    branch), or is there a different workaround?
*)

Lemma wp_operand_cfun2ptr_global (tu : translation_unit)
    (ρ : region) (name : obj_name) (f : Func) (ty : type)
    (Q : val -> FreeTemps -> mpred) :
  tu.(symbols) !! name = Some (Ofunction f) ->
  (exists body, f.(f_body) = Some body) ->
  denoteModule tu ** Q (Vptr (_global name)) FreeTemps.id
  |-- wp_operand tu ρ (Ecast Cfun2ptr (Eglobal name ty)) Q.
Proof. Admitted.

(** ** Gap 2: Reading a global const variable

    When C++ code reads a global const (e.g. [static const bool black = false]),
    the wp goal is:
<<
    wp_operand tu ρ (Ecast Cl2r (Eglobal name qty)) Q
>>
    Reducing via [wp_operand_cast_l2r] → [wp_lval_global] → [read_decl]
    eventually requires [initializedR] at the global's address to extract
    the stored value.  However, [denoteModule] only provides [svalidR]
    (location validity) via [denoteSymbol].  The gap is in [initSymbol],
    which returns [emp] with the comment in [translation_unit.v]:

<<
    (* ^^ todo(gmm): static initialization is not yet supported *)
>>

    Note: In the placeholder statement below, [v] is universally quantified
    but unconstrained by [init] — the "correct" statement would tie [v] to
    the result of evaluating the initializer.  We state it this way only
    because [initSymbol] returns [emp], so there is no infrastructure to
    express the constraint yet.  Our actual usage always instantiates [v]
    with the concrete value matching the initializer (e.g. [Vbool false]
    for [global_init.Init (Ebool false)]).

    Question: Is there a way to obtain [initializedR] for a global variable
    from the current axiom set, or is static initialization support still
    pending?
*)

Lemma wp_operand_read_global_const (tu : translation_unit)
    (ρ : region) (name : obj_name) (qty : type) (init : global_init.t)
    (v : val) (Q : val -> FreeTemps -> mpred) :
  tu.(symbols) !! name = Some (Ovar qty init) ->
  denoteModule tu ** Q v FreeTemps.id
  |-- wp_operand tu ρ (Ecast Cl2r (Eglobal name qty)) Q.
Proof. Admitted.

End gaps.

(** ** Summary

    1. [wp_operand_cfun2ptr_global] — blocked on [align_of] for [Tfunction].
    2. [wp_operand_read_global_const] — blocked on [initSymbol] returning [emp].

    Both appear to be framework-level gaps rather than user errors.  We are
    currently using these as [Admitted] placeholders.  Any guidance — whether
    a workaround exists, a fix is in progress, or we should restructure our
    approach — would be very helpful.  Thank you!
*)
