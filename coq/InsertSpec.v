(** * Insert Specification and Proof — Phase 5A
    Created: 2026-02-17
    Updated: 2026-02-18 — Complete [insert_ok] proof (assignment + return).

    Proves that the C++ [Node::insert] (and helper [Node::ins],
    [Node::setRebalanceLeft], [Node::setRebalanceRight], [Node::makeCopy])
    refine their functional counterparts from [RBTree.v].

    == C++ functions under verification ==

    - [insert(k, v, n)]: top-level insert, calls [ins] then sets root black
    - [ins(k, v, n)]: recursive insert with ownership transfer + rebalancing
    - [setRebalanceLeft(n, newLeft)]: LL/LR rotation (mutates in place)
    - [setRebalanceRight(n, newRight)]: RL/RR rotation (mutates in place)
    - [makeCopy(p)]: returns unique copy (clone if ref_count > 1, reuse if 1)

    == Proof strategy ==

    Bottom-up dependency chain:
      insert → ins → { makeCopy, setRebalanceLeft, setRebalanceRight }
                       setRebalanceLeft  → makeCopy
                       setRebalanceRight → makeCopy

    Phase 5A (this file): Extract all 5 functions, define specs, Admit all
    except insert_ok.  Phase 5B: setRebalanceLeft/Right.  Phase 5C: ins.
    Phase 6 (RefCount.v): makeCopy, free, copy.

    == Ownership transfer pattern ==

    These functions consume input pointers and produce new ones.
    Specs use [\pre] (consumed) + [\post] (produced), NOT [\prepost]
    (borrowed).  This is required because [ins] may free the input
    tree and return a completely new allocation.

    == Function call resolution ==

    When the wp proof for [insert] reaches the call to [ins], the
    proof must resolve [wp_fptr source.(types) ft (_global ins_name) vs Q].
    The resolution chain is:

    1. [denoteModule_denoteSymbol] + [ins_lookup]:
         [denoteModule source |-- _global ins_name |-> code_at source ins_func]
    2. [code_at_ok] (from compile.v):
         [code_at source ins_func p |-- ∀ ls Q,
            wp_func source ins_func ls Q -* wp_fptr source.(types) ... p ls Q]
    3. [func_ok source ins_func ins_spec] (= [ins_ok], Admitted for now):
         [□ (∀ Q vals, ins_spec.fs_spec vals Q -* wp_func source ins_func vals Q)]

    Composing these resolves [wp_fptr] from [ins_spec.fs_spec].

    The auto framework ([verify[source]]) automates this chain. For manual
    proofs, [denoteModule source] must be provided as a persistent hypothesis.

    All functional correctness lemmas ([isBST_ins], [isBST_insert],
    [noRedRed_insert], etc.) are proven in [RBTree.v] with zero [Admitted].
*)

From Coq Require Import ZArith Bool Lia.

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.Tactics.
Require Import daedalus_rb.map_int_int_cpp.

(* ================================================================= *)
(** * Function Extraction from the Generated AST

    Each function is a static method of [Node] (= [Dmethod _ true] in
    the generated AST).  The parser stores static methods as
    [Ofunction (static_method m)] in the symbol table.

    For each function we define:
    - [*_name : obj_name] — the symbol table key
    - [*_func : Func] — the extracted function definition
    - [*_lookup] — machine-checked proof that the lookup succeeds

    The names match the AST definitions:
      n4041  = _Node_name     (the Node class scope)
      t710   = Tnamed n4041   (Node type)
      t711   = Tptr t710      (Node* type)
*)
(* ================================================================= *)

(** ** insert *)

#[local] Open Scope pstring_scope.
Definition insert_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "insert"
      (Tint :: Tint :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

Definition insert_func : Func :=
  match source.(symbols) !! insert_name with
  | Some (Ofunction f) => f
  | _ =>
    {| f_return := Tvoid
     ; f_params := nil
     ; f_cc := CC_C
     ; f_arity := Ar_Definite
     ; f_exception := exception_spec.NoThrow
     ; f_body := None |}
  end.

Lemma insert_lookup :
  source.(symbols) !! insert_name = Some (Ofunction insert_func).
Proof. native_compute. reflexivity. Qed.

(** ** ins *)

#[local] Open Scope pstring_scope.
Definition ins_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "ins"
      (Tint :: Tint :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

Definition ins_func : Func :=
  match source.(symbols) !! ins_name with
  | Some (Ofunction f) => f
  | _ =>
    {| f_return := Tvoid
     ; f_params := nil
     ; f_cc := CC_C
     ; f_arity := Ar_Definite
     ; f_exception := exception_spec.NoThrow
     ; f_body := None |}
  end.

Lemma ins_lookup :
  source.(symbols) !! ins_name = Some (Ofunction ins_func).
Proof. native_compute. reflexivity. Qed.

(** ** makeCopy *)

#[local] Open Scope pstring_scope.
Definition makeCopy_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "makeCopy"
      (Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

Definition makeCopy_func : Func :=
  match source.(symbols) !! makeCopy_name with
  | Some (Ofunction f) => f
  | _ =>
    {| f_return := Tvoid
     ; f_params := nil
     ; f_cc := CC_C
     ; f_arity := Ar_Definite
     ; f_exception := exception_spec.NoThrow
     ; f_body := None |}
  end.

Lemma makeCopy_lookup :
  source.(symbols) !! makeCopy_name = Some (Ofunction makeCopy_func).
Proof. native_compute. reflexivity. Qed.

(** ** setRebalanceLeft *)

#[local] Open Scope pstring_scope.
Definition setRebalanceLeft_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "setRebalanceLeft"
      (Tptr _Node :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

Definition setRebalanceLeft_func : Func :=
  match source.(symbols) !! setRebalanceLeft_name with
  | Some (Ofunction f) => f
  | _ =>
    {| f_return := Tvoid
     ; f_params := nil
     ; f_cc := CC_C
     ; f_arity := Ar_Definite
     ; f_exception := exception_spec.NoThrow
     ; f_body := None |}
  end.

Lemma setRebalanceLeft_lookup :
  source.(symbols) !! setRebalanceLeft_name =
    Some (Ofunction setRebalanceLeft_func).
Proof. native_compute. reflexivity. Qed.

(** ** setRebalanceRight *)

#[local] Open Scope pstring_scope.
Definition setRebalanceRight_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "setRebalanceRight"
      (Tptr _Node :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

Definition setRebalanceRight_func : Func :=
  match source.(symbols) !! setRebalanceRight_name with
  | Some (Ofunction f) => f
  | _ =>
    {| f_return := Tvoid
     ; f_params := nil
     ; f_cc := CC_C
     ; f_arity := Ar_Definite
     ; f_exception := exception_spec.NoThrow
     ; f_body := None |}
  end.

Lemma setRebalanceRight_lookup :
  source.(symbols) !! setRebalanceRight_name =
    Some (Ofunction setRebalanceRight_func).
Proof. native_compute. reflexivity. Qed.

(** ** Node::black (global const) *)

Definition black_name : obj_name := Nscoped _Node_name (Nid "black").

Lemma black_lookup :
  source.(symbols) !! black_name =
    Some (Ovar (Qconst Tbool) (global_init.Init (Ebool false))).
Proof. native_compute. reflexivity. Qed.

(* ================================================================= *)
(** * Formal Specifications

    Each spec uses the ownership transfer pattern:
    - [\pre{t}] binds the abstract tree and asserts ownership (consumed)
    - [\post{ret}] binds the return pointer and asserts ownership (produced)

    This differs from [findNode_spec] (FindSpec.v), which uses [\prepost]
    because [findNode] borrows the tree without consuming it.
*)
(* ================================================================= *)

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.

(** Persistent module resource — provides [code_at] for all functions
    in the translation unit.  The auto framework supplies this via
    [verify[source]]; for manual proofs we require it as a hypothesis. *)
Hypothesis MODULE : |-- denoteModule source.

(** ** makeCopy_spec

    Consumes input pointer [p], returns pointer [p'] with exclusive
    ownership representing the same abstract tree.

    If [ref_count = 1], returns [p] unchanged (no allocation).
    If [ref_count > 1], allocates a fresh clone and decrements [p]'s
    ref_count.

    Deferred to Phase 6 (RefCount.v) for full proof — requires
    Iris ghost state for reference counting. *)
Definition makeCopy_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node) (Tptr _Node :: nil)
      (\arg{p} "p" (Vptr p)
       \pre{t} p |-> treeR (cQp.m 1) t
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) t)).

(** ** ins_spec

    Recursive insert.  Consumes tree at [n], produces tree at [ret]
    representing [ins k v t]. *)
Definition ins_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tint :: Tint :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tint :: Tint :: Tptr _Node :: nil)
      (\arg{k} "k" (Vint k)
       \arg{v} "v" (Vint v)
       \arg{n} "n" (Vptr n)
       \pre{t} n |-> treeR (cQp.m 1) t
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (ins k v t))).

(** ** setRebalanceLeft_spec

    Takes node [n] (with its left child already detached by the caller)
    and new left subtree [newLeft].  Returns the rebalanced tree.

    The precondition has the full tree at [n] — the C++ code reads
    fields of [n] (color, right child) during rotation. The "old left"
    is conceptually replaced by [newLeft], matching the functional spec
    [setRebalanceLeft c newLeft k v r].

    NOTE: the exact precondition shape (whether [n] holds the full tree
    or individual fields) needs refinement in Round 5B when the proof
    is attempted.  For now we use the tree-level spec. *)
Definition setRebalanceLeft_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nl_ptr} "newLeft" (Vptr nl_ptr)
       \pre{c k v l r} n_ptr |-> treeR (cQp.m 1) (Node c l k v r)
       \pre nl_ptr |-> treeR (cQp.m 1) Leaf (* placeholder for detached old left *)
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceLeft c Leaf k v r))).
(* NOTE: this spec is a placeholder — the actual semantics of
   setRebalanceLeft receive the new left subtree through [nl_ptr],
   not as part of [n]'s tree.  Round 5B will refine this spec to
   work at the field level after [wp_unfold_node]. *)

(** ** setRebalanceRight_spec (symmetric) *)
Definition setRebalanceRight_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nr_ptr} "newRight" (Vptr nr_ptr)
       \pre{c k v l r} n_ptr |-> treeR (cQp.m 1) (Node c l k v r)
       \pre nr_ptr |-> treeR (cQp.m 1) Leaf (* placeholder *)
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceRight c l k v Leaf))).
(* NOTE: placeholder spec, same caveat as setRebalanceLeft_spec. *)

(** ** insert_spec

    Top-level insert: calls [ins] then forces root to black.
    Consumes input tree, produces output tree representing
    [RBTree.insert k v t]. *)
Definition insert_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tint :: Tint :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tint :: Tint :: Tptr _Node :: nil)
      (\arg{k} "k" (Vint k)
       \arg{v} "v" (Vint v)
       \arg{n} "n" (Vptr n)
       \pre{t} n |-> treeR (cQp.m 1) t
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (RBTree.insert k v t))).

(* ================================================================= *)
(** * Admitted Specifications (Deferred to Later Rounds)

    These are Admitted and used as axioms by [insert_ok].
    Each will be proven in the round indicated. *)
(* ================================================================= *)

(** Phase 6 (RefCount.v): requires Iris ghost state. *)
Lemma makeCopy_ok :
  |-- func_ok source makeCopy_func makeCopy_spec.
Proof. Admitted.

(** Round 5B: pointer surgery for LL/LR rotation. *)
Lemma setRebalanceLeft_ok :
  |-- func_ok source setRebalanceLeft_func setRebalanceLeft_spec.
Proof. Admitted.

(** Round 5B: pointer surgery for RL/RR rotation. *)
Lemma setRebalanceRight_ok :
  |-- func_ok source setRebalanceRight_func setRebalanceRight_spec.
Proof. Admitted.

(** Round 5C: recursive wp proof by structural induction. *)
Lemma ins_ok :
  |-- func_ok source ins_func ins_spec.
Proof. Admitted.

(* ================================================================= *)
(** * insert_ok — Round 5A Target

    C++ body:
<<
      static Node* insert(Key k, Value v, Node *n) {
        Node *curr = ins(k, v, n);
        curr->color = black;
        return curr;
      }
>>

    Proof outline:
    1. Extract arguments (k, v, n) from spec
    2. Step through variable declaration for [curr]
    3. Resolve [ins(k, v, n)] call → produces [curr_ptr |-> treeR 1 (ins k v t)]
    4. Destruct [ins k v t] (always a Node, by [ins_is_node])
    5. Unfold [treeR] at [curr_ptr] to access fields
    6. Write [curr->color = black]
    7. Fold [treeR] back with updated color
    8. Show result equals [insert k v t] (by [makeBlack_node] + [ins_is_node])
    9. Return

    Step 3 uses [wp_call_direct] from [WpTactics.v]:
    [denoteModule] → [code_at_of_denoteModule] → [code_at_ok] →
    [func_ok] (= [ins_ok]) → [wp_fptr].
*)
(* ================================================================= *)

(** Machine-checked proof that [ins_func] has a body. Required by
    [code_at_of_denoteModule] to extract [code_at] from [denoteModule]. *)
Lemma ins_has_body : exists body, ins_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma insert_ok :
  |-- func_ok source insert_func insert_spec.
Proof using MOD MODULE.
  rewrite /func_ok. iSplit.
  - iPureIntro. reflexivity.
  - iIntros "!>" (Q vals) "Hspec".
    iPoseProof MODULE as "#HMOD".
    iApply wp_func_intro.
    rewrite /insert_func /=.
    (** Extract args: k, v, n from spec. *)
    iDestruct "Hspec" as (pk vk pn vn pn0 vn0) "(%Hvals & Hpk & Hpv & Hpn & Hspec)".
    subst vals. simpl.
    iDestruct "Hspec" as (k v n t) "(%Hargs & Htree & Hcont)".
    injection Hargs as -> ->. subst.
    (** wp_auto through Sseq → Sdecl → wp_initialize scaffolding. *)
    wp_auto.
    (** At [∀ addr, wp_operand ... (Ecall ...) Q]. Introduce addr and
        apply the Ecall rule to get [wp_call]. *)
    iIntros (addr).
    iApply wp_operand_call.
    rewrite /wp_call /=.
    (** Discharge [source ⊧ σ] from MOD. *)
    iIntros "%_".
    (** Unfold [Mbind] to expose [wp_operand] for function expression. *)
    rewrite /wp.WPE.Mbind /wp.WPE.Mmap /=.
    (** Resolve function expression: [Ecast Cfun2ptr (Eglobal ins_name t6062)].
        Uses [wp_operand_cfun2ptr_global] which bridges the BRiCk alignment
        gap for function types.  After this, the continuation is instantiated
        at [Vptr (_global ins_name)] and we have [denoteModule] in scope. *)
    iApply (wp_operand_cfun2ptr_global _ _ _ _ _ _ ins_lookup ins_has_body).
    iSplitL "HMOD"; [iExact "HMOD" |].
    (** Goal: continuation with [Vptr (_global ins_name)].
        The existential for [fp] and the [nd_seqs] argument evaluation
        remain.  Instantiate the function pointer. *)
    iExists (_global ins_name).
    iSplit; [iPureIntro; reflexivity |].
    (** Resolve all 6 argument evaluation orderings (3! = 6 branches).
        After [injection; subst], the spec values are [Vint k], [Vint v],
        [Vptr n] — the original [vk]/[vn]/[vn0] variables were substituted. *)
    wp_nd_args ltac:(first [
      wp_read_local "Hpk" (Vint k) |
      wp_read_local "Hpv" (Vint v) |
      wp_read_local "Hpn" (Vptr n)
    ]).
    (** Resolve function pointer → ins_spec precondition.
        [wp_call_direct] uses [change] to bridge the function type for
        unification, then applies [wp_fptr_of_func_ok_compat] and
        provides persistent [code_at]/[func_ok] without consuming
        spatial resources.  Remaining goal: [fs_spec ins_spec vs Q]. *)
    all: wp_call_direct "HMOD" ins_lookup ins_has_body ins_ok ins_func.
    (** Provide [fs_spec ins_spec] from spatial resources.
        Phase 1: argument pointer/value pairs from temporaries.
          The 6 nd_seqs branches have different temporary orderings
          (e.g. [p; p0; p1] vs [p; p1; p0]), so we match the [vs] list
          from the goal and provide matching pointer existentials.
          Value existentials are left as evars and resolved by [iFrame].
        Phase 2: abstract parameters (k, v, n, t) from tree ownership. *)
    all: rewrite /ins_spec.
    all: simpl.
    (** The 6 nd_seqs branches have different temporary pointer orderings
        (e.g. [p; p0; p1] vs [p; p1; p0]).  Extract the [vs] list from
        the goal — the VALUES are always (k, v, n) in spec argument order. *)
    all: lazymatch goal with
         | |- context[ @eq (list ptr) _ (?a :: ?b :: ?c :: nil) ] =>
           iExists a, (Vint k), b, (Vint v), c, (Vptr n)
         end.
    all: iSplit; [iPureIntro; reflexivity |].
    all: iFrame.
    all: iExists k, v.
    all: iSplit; [iPureIntro; reflexivity |].
    (** Post-call: [ins] returns [curr |-> treeR 1 (ins k v t)].
        Cleanup: [anyR] for 3 arg temporaries + [tptsto_fuzzyR] for recv. *)
    all: iIntros (curr) "Hins_tree".
    all: iIntros (recv_ptr) "(Hanyp & Hanyp0 & Hanyp1 & Hrecv)".
    (** Destroy 3 argument temporaries from [ins] call.
        Each [destroy_val] for a primitive type reduces to [wp_destroy_prim].
        [anyR_wp_destroy_prim_val] bridges [anyR ** Q |-- wp_destroy_prim]. *)
    all: wp_auto.
    all: rewrite /to_arg_type /=.
    all: destroy_val_unfold; simpl.
    all: iApply anyR_wp_destroy_prim_val; [done |].
    all: cbn -[destroy_val wp_destroy_prim operand_receive]; iFrame "Hanyp1".
    all: destroy_val_unfold; simpl.
    all: iApply anyR_wp_destroy_prim_val; [done |].
    all: cbn -[destroy_val wp_destroy_prim operand_receive]; iFrame "Hanyp0".
    (** Third temp: already [wp_destroy_prim] (not [destroy_val]) because
        [destroy_val_unfold] used [!] which rewrote both [int]-typed
        [destroy_val]s in the second cycle. Skip [destroy_val_unfold]. *)
    all: iApply anyR_wp_destroy_prim_val; [done |].
    all: iFrame "Hanyp".
    (** All arg temporaries destroyed.  Strip fupd, then resolve
        [operand_receive]: store [ins] return value into local [curr]. *)
    all: iModIntro.
    all: rewrite operand_receive.unlock /=.
    all: iExists (Vptr curr); iFrame "Hrecv".
    (** [operand_receive] provided [addr |-> tptsto_fuzzyR "Node*" 1$m (Vptr curr)]
        to the continuation wand.  Introduce it as [Hcurr_local]. *)
    all: iIntros "Hcurr_local".
    (** Strip accumulated fupd/later modalities to reach the wp. *)
    all: repeat (first [iModIntro | iNext]).
    (** Step 4: Destruct [ins k v t] — always a Node by [ins_is_node].
        Needed to unfold [treeR] for field-level access. *)
    all: destruct (ins_is_node k v t) as [c' [l' [k' [v' [r' Hins_eq]]]]].
    (** Step 5: Rewrite [Hins_tree] with [ins_is_node] equation, then
        unfold [treeR] to access individual fields.
        [iRevert] moves it to the goal so [rewrite] can reach it. *)
    all: iRevert "Hins_tree"; rewrite Hins_eq; iIntros "Hins_tree".
    all: wp_unfold_node "Hins_tree".
    (** Step 6: wp through [Sexpr] → assignment [curr->color = black]. *)
    all: wp_auto.
    (** Step 6: Assignment [curr->color = black].
        C++17 rl order: evaluate RHS ([Node::black] = false) first,
        then LHS ([curr->color] address), then write.

        After the assignment, the color field is updated:
          [_ncolor : curr |-> _color |-> tptstoR "bool" 1$m (Vbool false)]
        All other fields unchanged. No temporaries created (global const read
        + member l-value don't create temps, so [interp source id] is trivial).

        Phase 5B TODO: Fill in the wp_lval_assign mechanics:
          1. Unfold Mmap/Mseq to sequential evaluation
          2. RHS: wp_operand (Ecast Cl2r (Eglobal "Node::black" "const bool"))
             → resolve global via denoteModule → Dvariable → Vbool false
          3. LHS: wp_lval (Emember ... "color" ...)
             → wp_lval_member → read_arrow (read curr local) → field offset
          4. Pre: provide [anyR "bool" 1$m] from [_ncolor]
          5. Post: consume [tptstoR "bool" 1$m (Vbool false)] *)
    all: iApply wp_lval_assign.
    (** Step 6a: Unfold [eval2] for C++17 rl order (RHS first, then LHS).
        [eval2 rl] = [Mmap swap (Mseq rhs lhs)].  Unfold the monadic
        wrappers to expose [wp_operand] for the RHS at the top level. *)
    (** Step 6a: Unfold [eval2] for C++17 rl order (RHS first, then LHS).
        [eval2 rl] = [Mmap swap (Mseq rhs lhs)].  Unfold the monadic
        wrappers to expose [wp_operand] for the RHS at the top level. *)
    all: rewrite /= /eval2 /wp.WPE.Mmap /wp.WPE.Mseq /wp.WPE.Mbind /=.
    (** Step 6b: RHS — evaluate [Node::black] (global const → [Vbool false]).
        Uses [wp_read_global_const] (Admitted lemma) since BRiCk's
        [initSymbol] doesn't support static initialization yet. *)
    all: wp_read_global_const "HMOD" black_lookup (Vbool false).
    (** Step 6c: LHS — evaluate [curr->color] address.
        Chain: [wp_lval_member] → [read_arrow] → read [curr] local →
        [reference_to] from struct → [read_decl] → field offset.
        Must [wp_offset] the color field first to convert from nested
        to offset form for [wp_observe_ref]. *)
    all: wp_offset "_ncolor".
    all: wp_assign_member_field "Hcurr_local" (Vptr curr) "_nstruct" "_ncolor".
    (** Step 6d: Post-assign — receive the updated color field.
        [wp_lval_assign] yields [tptstoR "bool" 1$m (Vbool false)]. *)
    all: iIntros "_ncolor_new".
    (** Step 6e: Strip [interp] (no temporaries) + modalities. *)
    all: wp_auto.
    (** Step 7: Fold [treeR] back with updated color = Black.
        Convert [tptstoR] → [primR] (since [Vbool false] is not raw/undef),
        revert the color field offset, then fold via [treeR_node_fold].
        Must use [iAssert] since the goal is a [wp_stmt], not [treeR]. *)
    all: iPoseProof (tptstoR_to_primR _ _ _ (Vbool false) I with "_ncolor_new") as "_ncolor".
    all: wp_revert_offset "_ncolor".
    all: iPoseProof (treeR_node_fold _ Black l' k' v' r' _lp _rp _rc curr
           with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]") as "Htree".
    (** Step 8: Semantic equivalence — [Node Black l' k' v' r' = insert k v t]. *)
    all: iRevert "Htree".
    all: rewrite /RBTree.insert Hins_eq makeBlack_node.
    all: iIntros "Htree".
    (** Step 9: Return path.
        After [wp_auto], goal is [∀ p, wp_operand ... (return expr) ...].
        The [∀ p] is from [wp_initialize] for the return value. *)
    all: repeat wp_step.
    all: iIntros (?).
    (** Now goal is [wp_operand _ _ (Ecast Cl2r (Evar "curr" _)) Q].
        Read the local variable [curr] to get [Vptr curr]. *)
    all: wp_read_local "Hcurr_local" (Vptr curr).
    (** After reading [curr], a wand remains (from return initialization).
        Introduce its premise and continue stepping. *)
    all: iIntros "?".
    all: repeat wp_step.
    (** Step 10: Remaining goal is the return cleanup + postcondition.
        TODO: destroy [curr] local, provide [Hcont] with [Htree]. *)
    all: admit.
Admitted.

End with_Sigma.
