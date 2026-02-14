(** * Invariant Glue Proofs

    Composes the refinement proofs (FindSpec, InsertSpec, RefCount) with
    the functional invariant proofs (RBTree.v) to establish end-to-end
    correctness guarantees for the C++ [DDL::Map<int,int>].

    == End-to-end properties ==

    For a tree [t] built by repeated [insert] from empty:

    1. **BST ordering**: [IsBST t] — in-order traversal yields strictly
       ascending keys. (Functional proof in RBTree.v, refined to C++ in
       InsertSpec.v.)

    2. **Red-black balance**: [NoRedRed t] — no red node has a red child.
       Combined with uniform black-depth (implied by the rotation structure),
       this guarantees O(log n) height. (Functional proof in RBTree.v.)

    3. **findNode correctness**: looking up key [k] returns [Some v] iff
       [k] was the most recently inserted key with value [v]. (Functional
       spec in RBTree.v, C++ refinement in FindSpec.v.)

    4. **Memory safety**: no use-after-free, no double-free, no leaks for
       trees with unique ownership. (RefCount.v.)

    == Phase 7 TODO ==

    After all operation proofs are complete:
    1. Import and compose all specs
    2. State the top-level correctness theorem
    3. Prove by composing operation refinements with functional invariants
*)

From Coq Require Import ZArith List.
Import ListNotations.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.FindSpec.
Require Import daedalus_rb.InsertSpec.
Require Import daedalus_rb.RefCount.

(** ** Trees built from empty satisfy all invariants *)

(** The empty tree is a valid BST. *)
Lemma isBST_empty : IsBST (Leaf (K:=Z) (V:=Z)).
Proof. simpl. exact I. Qed.

(** The empty tree has no red-red violations. *)
Lemma noRedRed_empty : NoRedRed (Leaf (K:=Z) (V:=Z)).
Proof. simpl. exact I. Qed.

(** Folding [insert] over a list preserves BST, starting from empty. *)
Lemma fromList_isBST : forall kvs,
  IsBST (fromList kvs).
Proof.
  unfold fromList. intros.
  (* Induction on kvs, using isBST_insert at each step *)
Admitted.

(** Folding [insert] over a list preserves NoRedRed. *)
Lemma fromList_noRedRed : forall kvs,
  NoRedRed (fromList kvs).
Proof.
  unfold fromList. intros.
  (* Induction on kvs, using noRedRed_insert at each step *)
Admitted.

(** ** findNode correctness for trees built by insert *)

(** After inserting [(k, v)], looking up [k] returns [v]. *)
Lemma findNode_after_insert : forall k v t,
  IsBST t ->
  findNode k (insert k v t) = Some v.
Proof.
  (* Induction on t, using properties of ins and makeBlack *)
Admitted.

(** Inserting a different key doesn't affect lookup. *)
Lemma findNode_insert_other : forall k k' v t,
  k <> k' ->
  IsBST t ->
  findNode k (insert k' v t) = findNode k t.
Proof.
  (* Induction on t, using properties of ins and makeBlack *)
Admitted.

(** ** Top-level correctness theorem (scaffold)

    This is the capstone theorem composing all the pieces. *)

(** For any sequence of key-value pairs, building a tree via [fromList]
    and then looking up a key returns the value from the last insertion
    of that key. *)
Theorem fromList_lookup_correct : forall kvs k v,
  (* k was inserted with value v, and no later insertion overwrites k *)
  (* (precise statement requires tracking the last occurrence in kvs) *)
  IsBST (fromList kvs) ->
  True. (* PLACEHOLDER: full statement is complex *)
Proof.
Admitted.

(** ** C++ refinement composition (scaffold)

    When the BRiCk wp proofs are complete, this theorem will compose:
    - C++ insert refines functional insert (InsertSpec.v)
    - C++ findNode refines functional findNode (FindSpec.v)
    - Functional insert preserves BST + NoRedRed (RBTree.v)
    - Reference counting is sound (RefCount.v)

    Into: the C++ Map implementation is a correct, memory-safe BST. *)

(** Top-level C++ correctness:

    For any sequence of insert/lookup operations on a Map<int,int>,
    the C++ implementation produces the same observable results as
    the functional specification, and is memory-safe.

    {{{ emp }}}
      Map<int,int> m;
      m = m.insert(k1, v1);
      ...
      m = m.insert(kn, vn);
      bool found = m.contains(k);
    {{{ ⌜found = (findNode k (fromList [(k1,v1);...;(kn,vn)])).isSome⌝ }}}
*)
