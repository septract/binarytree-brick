(** * Separation Logic Representation Predicate

    Links the Coq [tree Z Z] type from [RBTree.v] to the C++ [Node] heap
    layout in the cpp2v-generated deep embedding.

    The predicate [tree_rep] states: "the C++ pointer [p] points to a heap
    region whose shape and contents match the abstract tree [t]."

    This file is a scaffold. The actual field names and types will be filled
    in after inspecting the cpp2v-generated [map_int_int_cpp_names.v], which
    contains the mangled C++ symbol table.

    == Design ==

    BRiCk represents C++ programs as deeply embedded Coq terms. The
    [wp_*] tactics discharge Hoare triples over these terms. To connect
    the C++ execution to our functional spec, we define:

      tree_rep : tree Z Z -> val -> iProp

    where [val] is BRiCk's type for C++ values (pointers, integers, etc.)
    and [iProp] is the Iris separation logic proposition type.

    The key clauses are:

    - [Leaf] ↔ the C++ pointer is null.
    - [Node c l k v r] ↔ the pointer is non-null and points to an
      allocated struct with fields [ref_count], [color], [key], [value],
      [left], [right] whose values match [c], [k], [v] and whose [left]
      and [right] pointers recursively satisfy [tree_rep l] and [tree_rep r].

    == Phase 3 TODO ==

    After running cpp2v (Phase 1), inspect [map_int_int_cpp_names.v] for:
    - The mangled struct name for [DDL::Map<int,int>::Node]
    - Field offset/name constants for [ref_count], [color], [key], etc.
    - The BRiCk representation of [bool] (for color) and [int]

    Then replace the [Admitted] placeholders below with proper definitions.
*)

From Coq Require Import ZArith.
(* After setup, uncomment:
From bedrock.lang.cpp Require Import semantics logic.
From bedrock.lang.cpp.logic Require Import wp.
From iris.proofmode Require Import proofmode.
*)

Require Import daedalus_rb.RBTree.

(** ** Placeholder types

    These will be replaced by BRiCk's actual types once the generated
    AST is available and the BRiCk Coq libraries are importable. *)

(* Placeholder for BRiCk's C++ value type *)
Definition val : Type := Z.  (* PLACEHOLDER: replace with bedrock val *)

(* Placeholder for Iris iProp *)
Definition iProp : Type := Prop.  (* PLACEHOLDER: replace with iPropI Σ *)

(** ** Color encoding

    The C++ code uses [bool] for color: [red = true], [black = false]. *)
Definition color_to_bool (c : Color) : bool :=
  match c with
  | Red => true
  | Black => false
  end.

(** ** Representation predicate (scaffold)

    The real definition will use BRiCk's [_at] points-to assertions and
    Iris separating conjunction [∗]. For now we state the intended shape
    as a Prop-level specification. *)

(** [tree_rep t p] asserts that C++ pointer [p] represents abstract tree [t].

    - [Leaf] maps to the null pointer.
    - [Node c l k v r] maps to a non-null pointer to an allocated struct
      whose fields match [c], [k], [v] and whose children recursively
      satisfy [tree_rep]. *)
Fixpoint tree_rep_spec (t : tree Z Z) (p : val) : Prop :=
  match t with
  | Leaf =>
      (* Null pointer *)
      p = 0%Z
  | Node c l k v r =>
      (* Non-null pointer to an allocated Node *)
      p <> 0%Z
      (* TODO: replace with separation logic points-to assertions:
         p |-> { ref_count : _, color : color_to_bool c,
                 key : k, value : v, left : pl, right : pr }
         ** tree_rep l pl
         ** tree_rep r pr *)
  end.

(** ** Basic lemmas (scaffold) *)

(** A Leaf is represented only by the null pointer. *)
Lemma tree_rep_leaf_null : forall p,
  tree_rep_spec Leaf p -> p = 0%Z.
Proof. intros p H. exact H. Qed.

(** A Node is never represented by the null pointer. *)
Lemma tree_rep_node_nonnull : forall c l k v r p,
  tree_rep_spec (Node c l k v r) p -> p <> 0%Z.
Proof. intros. simpl in H. exact H. Qed.
