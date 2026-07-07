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

(** ** is_black *)

#[local] Open Scope pstring_scope.
Definition is_black_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "is_black"
      (Tptr (Qconst _Node) :: nil)).
#[local] Close Scope pstring_scope.

(** ** is_red *)

#[local] Open Scope pstring_scope.
Definition is_red_name : obj_name :=
  Nscoped _Node_name
    (Nfunction function_qualifiers.N "is_red"
      (Tptr (Qconst _Node) :: nil)).
#[local] Close Scope pstring_scope.

(** ** Node::black (global const) *)

Definition black_name : obj_name := Nscoped _Node_name (Nid "black").

(* ================================================================= *)
(** * Function Extraction Helper *)
(* ================================================================= *)

(** Default [Func] for unreachable match branches. *)
#[local] Definition default_func : Func :=
  {| f_return := Tvoid
   ; f_params := nil
   ; f_cc := CC_C
   ; f_arity := Ar_Definite
   ; f_exception := exception_spec.NoThrow
   ; f_body := None |}.

(** Extract a [Func] from the symbol table by name.
    Returns [default_func] for missing/non-function entries
    (unreachable for names verified by lookup proofs below). *)
#[local] Definition extract_func (name : obj_name) : Func :=
  match source.(symbols) !! name with
  | Some (Ofunction f) => f
  | _ => default_func
  end.

(* ================================================================= *)
(** * Pre-computed Concrete Func Records

    [Eval vm_compute] evaluates [extract_func] at definition time
    and stores the concrete [Func] record in the [.vo] file.
    Subsequent imports unfold these to concrete values instantly. *)
(* ================================================================= *)

Definition insert_func : Func := Eval vm_compute in extract_func insert_name.
Definition ins_func : Func := Eval vm_compute in extract_func ins_name.
Definition makeCopy_func : Func := Eval vm_compute in extract_func makeCopy_name.
Definition setRebalanceLeft_func : Func := Eval vm_compute in extract_func setRebalanceLeft_name.
Definition setRebalanceRight_func : Func := Eval vm_compute in extract_func setRebalanceRight_name.
Definition is_black_func : Func := Eval vm_compute in extract_func is_black_name.
Definition is_red_func : Func := Eval vm_compute in extract_func is_red_name.

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

Lemma is_black_lookup :
  source.(symbols) !! is_black_name = Some (Ofunction is_black_func).
Proof. native_compute. reflexivity. Qed.

Lemma is_red_lookup :
  source.(symbols) !! is_red_name = Some (Ofunction is_red_func).
Proof. native_compute. reflexivity. Qed.

Lemma black_lookup :
  source.(symbols) !! black_name =
    Some (Ovar (Qconst Tbool) (global_init.Init (Ebool false))).
Proof. native_compute. reflexivity. Qed.

(** Machine-checked proofs that functions have bodies.  Required by
    [code_at_of_denoteModule] to extract [code_at] from [denoteModule]. *)
Lemma ins_has_body : exists body, ins_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma is_black_has_body : exists body, is_black_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma is_red_has_body : exists body, is_red_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma setRebalanceLeft_has_body :
  exists body, setRebalanceLeft_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma setRebalanceRight_has_body :
  exists body, setRebalanceRight_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma makeCopy_has_body : exists body, makeCopy_func.(f_body) = Some body.
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

(** ** setRebalanceLeft_spec

    Field-level ownership at [n]: the caller has consumed the left subtree
    (via recursive [ins]) and retains field-level struct ownership plus the
    right subtree.  The stale left pointer [lp] is never read — every code
    path overwrites it before use.  [newL] is the full tree from [ins]. *)
Definition setRebalanceLeft_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nl_ptr} "newLeft" (Vptr nl_ptr)
       \pre{c k v lp rp rc r newL}
         n_ptr |-> (_ref_count |-> ulongR (cQp.m 1) rc **
                    _color     |-> boolR (cQp.m 1) (color_to_bool c) **
                    _key       |-> intR (cQp.m 1) k **
                    _value     |-> intR (cQp.m 1) v **
                    _left      |-> ptrR<_Node> (cQp.m 1) lp **
                    _right     |-> ptrR<_Node> (cQp.m 1) rp **
                    structR _Node_name (cQp.m 1)) **
         rp |-> treeR (cQp.m 1) r **
         nl_ptr |-> treeR (cQp.m 1) newL
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceLeft c newL k v r))).

(** ** setRebalanceRight_spec

    Mirror of [setRebalanceLeft_spec]: the caller has consumed the right
    subtree (via recursive [ins]) and retains field-level struct ownership
    plus the left subtree. *)
Definition setRebalanceRight_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nr_ptr} "newRight" (Vptr nr_ptr)
       \pre{c k v lp rp rc l newR}
         n_ptr |-> (_ref_count |-> ulongR (cQp.m 1) rc **
                    _color     |-> boolR (cQp.m 1) (color_to_bool c) **
                    _key       |-> intR (cQp.m 1) k **
                    _value     |-> intR (cQp.m 1) v **
                    _left      |-> ptrR<_Node> (cQp.m 1) lp **
                    _right     |-> ptrR<_Node> (cQp.m 1) rp **
                    structR _Node_name (cQp.m 1)) **
         lp |-> treeR (cQp.m 1) l **
         nr_ptr |-> treeR (cQp.m 1) newR
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceRight c l k v newR))).

(** ** is_black_spec

    Minimal field-level: only needs [_color + structR] for non-null.
    [option Color] covers both null (black by convention) and non-null.
    [\prepost] returns resources unchanged — [is_black] is read-only.

    The C++ type is [Node const*] = [Tptr (Qconst _Node)]. *)
Definition is_black_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) Tbool
    (Tptr (Qconst _Node) :: nil)
    (cpp_spec (ar:=Ar_Definite) Tbool
      (Tptr (Qconst _Node) :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \prepost{c_opt : option Color}
         match c_opt with
         | None => [| n_ptr = nullptr |]
         | Some c => Exists (q : Qp),
             n_ptr |-> (_color |-> boolR q (color_to_bool c) **
                        structR _Node_name q)
         end
       \post{ret : ptr}[Vbool (match c_opt with
                                  | None => true
                                  | Some Black => true
                                  | Some Red => false end)]
         emp)).

(** ** is_red_spec

    Negation of [is_black_spec]. Same ownership pattern. *)
Definition is_red_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) Tbool
    (Tptr (Qconst _Node) :: nil)
    (cpp_spec (ar:=Ar_Definite) Tbool
      (Tptr (Qconst _Node) :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \prepost{c_opt : option Color}
         match c_opt with
         | None => [| n_ptr = nullptr |]
         | Some c => Exists (q : Qp),
             n_ptr |-> (_color |-> boolR q (color_to_bool c) **
                        structR _Node_name q)
         end
       \post{ret : ptr}[Vbool (match c_opt with
                                  | None => false
                                  | Some Black => false
                                  | Some Red => true end)]
         emp)).

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

Lemma is_black_ok :
  |-- func_ok source is_black_func is_black_spec.
Proof. Admitted.

Lemma is_red_ok :
  |-- func_ok source is_red_func is_red_spec.
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
