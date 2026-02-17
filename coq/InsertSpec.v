(** * Insert Specification and Proof — Phase 5A
    Created: 2026-02-17

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

    Step 3 is the function call resolution — see module header for the
    chain: [denoteModule] → [code_at_ok] → [func_ok] → [wp_fptr].

    TODO(Round 5D): Resolve function call mechanics.  Currently Admitted
    because the manual proof requires [denoteModule source] in the Iris
    context (normally provided by the auto framework's [verify_spec]).
    Options:
    (a) Import [skylabs.auto.cpp.prelude.proof] and use [verify[source]]
    (b) Add [denoteModule source] as a Section hypothesis
    (c) Write a custom [wp_call_func] tactic
*)
(* ================================================================= *)

Lemma insert_ok :
  |-- func_ok source insert_func insert_spec.
Proof using MOD.
  (* TODO: Full proof requires resolving the call to [ins] inside
     [insert]'s body.  This needs either:
     - The auto framework ([verify[source] insert_spec] + [verify_spec])
     - Manual [denoteModule source] hypothesis + [code_at_ok] + [ins_ok]

     The proof structure (after call resolution) is:
     1. [ins(k,v,n)] returns [curr_ptr |-> treeR 1 (ins k v t)]
     2. Destruct [ins k v t = Node c' l' k' v' r'] via [ins_is_node]
     3. [wp_unfold_node] on [curr_ptr] to access [_ncolor] field
     4. Write [curr->color = black]: updates [_ncolor] from [c'] to [Black]
     5. [treeR_node_fold] to reconstruct [treeR 1 (Node Black l' k' v' r')]
     6. Rewrite via [makeBlack_node]: [Node Black l' k' v' r' = makeBlack (ins k v t)]
     7. Unfold [insert]: [makeBlack (ins k v t) = insert k v t]
     8. Return [curr_ptr]

     See [2026-02-17_insert_proof_strategy.md] for the full call resolution
     chain involving [code_at_ok] from [compile.v]. *)
Admitted.

End with_Sigma.
