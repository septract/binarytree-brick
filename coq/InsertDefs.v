(** * Insert Function Definitions — Pre-computed AST Extraction
    Created: 2026-02-20

    Extracts insert-related function definitions from the cpp2v-generated
    AST via [Eval vm_compute], so that the concrete [Func] records are
    stored in the compiled [.vo] file.  Importing this module gives
    instant access to function bodies (no symbol table traversal).

    Also contains: symbol table lookup proofs ([native_compute]),
    formal specifications, and Admitted callee proofs.

    == Rationale ==

    [InsertSpec.v] previously defined [insert_func] as
    [match source.(symbols) !! insert_name with ...].  Every time Coq
    unfolded this (on each rebuild), it re-traversed the 96K-line symbol
    table.  Six [native_compute; reflexivity] lookup proofs each scanned
    the full table too.  Together these added several minutes per rebuild.

    By using [Eval vm_compute in ...], the concrete [Func] record is
    evaluated once at definition time and stored in the [.vo].  When
    [InsertSpec.v] imports [InsertDefs.vo], unfolding [insert_func]
    yields the concrete record instantly.

    The [native_compute] lookup proofs are also cached in the [.vo]:
    they verify that the pre-computed [Func] matches the actual AST
    entry, but only run during compilation of this file.
*)

From Stdlib Require Import ZArith Bool Lia.

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.
(** Re-export [map_int_int_cpp] so importers can reference
    [map_int_int_cpp.source] in section contexts without a
    separate [Require Import].  Loading the [.vo] is cheap —
    the expensive part (symbol table traversal) only happens
    when definitions like [insert_func_raw] are unfolded, and
    those are [#[local]] here. *)
Require Export daedalus_rb.map_int_int_cpp.

(* ================================================================= *)
(** * Function Names *)
(* ================================================================= *)

(** ** insert *)

#[local] Open Scope pstring_scope.
Definition insert_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "insert"
      (Tint :: Tint :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

(** ** ins *)

#[local] Open Scope pstring_scope.
Definition ins_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "ins"
      (Tint :: Tint :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

(** ** makeCopy *)

#[local] Open Scope pstring_scope.
Definition makeCopy_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "makeCopy"
      (Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

(** ** setRebalanceLeft *)

#[local] Open Scope pstring_scope.
Definition setRebalanceLeft_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "setRebalanceLeft"
      (Tptr _Node :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

(** ** setRebalanceRight *)

#[local] Open Scope pstring_scope.
Definition setRebalanceRight_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "setRebalanceRight"
      (Tptr _Node :: Tptr _Node :: nil)).
#[local] Close Scope pstring_scope.

(** ** Node::black (global const) *)

Definition black_name : obj_name := Nscoped _Node_name (Nid "black").

(* ================================================================= *)
(** * Raw Extractions (local — only used for lookup proofs) *)
(* ================================================================= *)

(** Default [Func] for unreachable match branches. *)
#[local] Definition default_func : Func :=
  {| f_return := Tvoid
   ; f_params := nil
   ; f_cc := CC_C
   ; f_arity := Ar_Definite
   ; f_exception := exception_spec.NoThrow
   ; f_body := None |}.

#[local] Definition insert_func_raw : Func :=
  match source.(symbols) !! insert_name with
  | Some (Ofunction f) => f
  | _ => default_func
  end.

#[local] Definition ins_func_raw : Func :=
  match source.(symbols) !! ins_name with
  | Some (Ofunction f) => f
  | _ => default_func
  end.

#[local] Definition makeCopy_func_raw : Func :=
  match source.(symbols) !! makeCopy_name with
  | Some (Ofunction f) => f
  | _ => default_func
  end.

#[local] Definition setRebalanceLeft_func_raw : Func :=
  match source.(symbols) !! setRebalanceLeft_name with
  | Some (Ofunction f) => f
  | _ => default_func
  end.

#[local] Definition setRebalanceRight_func_raw : Func :=
  match source.(symbols) !! setRebalanceRight_name with
  | Some (Ofunction f) => f
  | _ => default_func
  end.

(* ================================================================= *)
(** * Pre-computed Concrete Func Records

    [Eval vm_compute] evaluates the raw extraction at definition time
    and stores the concrete [Func] record in the [.vo] file.
    Subsequent imports unfold these to concrete values instantly. *)
(* ================================================================= *)

Definition insert_func : Func := Eval vm_compute in insert_func_raw.
Definition ins_func : Func := Eval vm_compute in ins_func_raw.
Definition makeCopy_func : Func := Eval vm_compute in makeCopy_func_raw.
Definition setRebalanceLeft_func : Func := Eval vm_compute in setRebalanceLeft_func_raw.
Definition setRebalanceRight_func : Func := Eval vm_compute in setRebalanceRight_func_raw.

(* ================================================================= *)
(** * Lookup Proofs (cached in .vo via native_compute) *)
(* ================================================================= *)

Lemma insert_lookup :
  source.(symbols) !! insert_name = Some (Ofunction insert_func).
Proof. native_compute. reflexivity. Qed.

Lemma ins_lookup :
  source.(symbols) !! ins_name = Some (Ofunction ins_func).
Proof. native_compute. reflexivity. Qed.

Lemma makeCopy_lookup :
  source.(symbols) !! makeCopy_name = Some (Ofunction makeCopy_func).
Proof. native_compute. reflexivity. Qed.

Lemma setRebalanceLeft_lookup :
  source.(symbols) !! setRebalanceLeft_name =
    Some (Ofunction setRebalanceLeft_func).
Proof. native_compute. reflexivity. Qed.

Lemma setRebalanceRight_lookup :
  source.(symbols) !! setRebalanceRight_name =
    Some (Ofunction setRebalanceRight_func).
Proof. native_compute. reflexivity. Qed.

Lemma black_lookup :
  source.(symbols) !! black_name =
    Some (Ovar (Qconst Tbool) (global_init.Init (Ebool false))).
Proof. native_compute. reflexivity. Qed.

(** Machine-checked proof that [ins_func] has a body. Required by
    [code_at_of_denoteModule] to extract [code_at] from [denoteModule]. *)
Lemma ins_has_body : exists body, ins_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.

(* ================================================================= *)
(** * Formal Specifications

    Each spec uses the ownership transfer pattern:
    - [\pre{t}] binds the abstract tree and asserts ownership (consumed)
    - [\post{ret}] binds the return pointer and asserts ownership (produced)

    This differs from [findNode_spec] (FindSpec.v), which uses [\prepost]
    because [findNode] borrows the tree without consuming it. *)
(* ================================================================= *)

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.

(** ** makeCopy_spec *)
Definition makeCopy_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node) (Tptr _Node :: nil)
      (\arg{p} "p" (Vptr p)
       \pre{t} p |-> treeR (cQp.m 1) t
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) t)).

(** ** ins_spec *)
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

(** ** setRebalanceLeft_spec *)
Definition setRebalanceLeft_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nl_ptr} "newLeft" (Vptr nl_ptr)
       \pre{c k v l r} n_ptr |-> treeR (cQp.m 1) (Node c l k v r)
       \pre nl_ptr |-> treeR (cQp.m 1) Leaf
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceLeft c Leaf k v r))).

(** ** setRebalanceRight_spec *)
Definition setRebalanceRight_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nr_ptr} "newRight" (Vptr nr_ptr)
       \pre{c k v l r} n_ptr |-> treeR (cQp.m 1) (Node c l k v r)
       \pre nr_ptr |-> treeR (cQp.m 1) Leaf
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceRight c l k v Leaf))).

(** ** insert_spec *)
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
(** * Admitted Callee Specifications (Deferred to Later Rounds) *)
(* ================================================================= *)

Lemma makeCopy_ok :
  |-- func_ok source makeCopy_func makeCopy_spec.
Proof. Admitted.

Lemma setRebalanceLeft_ok :
  |-- func_ok source setRebalanceLeft_func setRebalanceLeft_spec.
Proof. Admitted.

Lemma setRebalanceRight_ok :
  |-- func_ok source setRebalanceRight_func setRebalanceRight_spec.
Proof. Admitted.

Lemma ins_ok :
  |-- func_ok source ins_func ins_spec.
Proof. Admitted.

End with_Sigma.
