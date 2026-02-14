(** * Invariant Glue Proofs

    Composes the refinement proofs (FindSpec, InsertSpec, RefCount) with
    the functional invariant proofs (RBTree.v) to establish end-to-end
    correctness guarantees for the C++ [DDL::Map<int,int>].

    == End-to-end properties ==

    For a tree [t] built by repeated [insert] from empty:

    1. **BST ordering**: [IsBST t] — in-order traversal yields strictly
       ascending keys. (Proven: [fromList_isBST] in RBTree.v.)

    2. **Red-black balance**: [NoRedRed t] — no red node has a red child.
       Combined with uniform black-depth (implied by the rotation structure),
       this guarantees O(log n) height. (Proven: [fromList_noRedRed] in RBTree.v.)

    3. **findNode correctness**: looking up key [k] returns [Some v] iff
       [k] was the most recently inserted key with value [v].
       (Proven: [findNode_after_insert], [findNode_insert_other] in RBTree.v.)

    4. **Memory safety**: no use-after-free, no double-free, no leaks for
       trees with unique ownership. (Phase 6: RefCount.v.)

    == Current status ==

    All functional invariant proofs are complete in [RBTree.v] (zero
    [Admitted]). This file provides trivial base cases and the scaffold
    for the C++ refinement composition (Phase 7).

    == Phase 7 TODO ==

    After all operation proofs are complete:
    1. Import FindSpec, InsertSpec, RefCount
    2. State the top-level C++ correctness theorem
    3. Prove by composing operation refinements with functional invariants
*)

From Coq Require Import ZArith List.
Import ListNotations.

Require Import daedalus_rb.RBTree.

(** ** Trees built from empty satisfy all invariants *)

(** The empty tree is a valid BST. *)
Lemma isBST_empty : IsBST (Leaf (K:=Z) (V:=Z)).
Proof. simpl. exact I. Qed.

(** The empty tree has no red-red violations. *)
Lemma noRedRed_empty : NoRedRed (Leaf (K:=Z) (V:=Z)).
Proof. simpl. exact I. Qed.

(** ** Summary of proven invariants (from RBTree.v)

    The following key theorems are all proven with zero [Admitted] in
    [RBTree.v]. They are listed here for reference — import [RBTree]
    to use them directly.

    - [isBST_insert]: insert preserves BST ordering
    - [noRedRed_insert]: insert preserves red-black balance
    - [fromList_isBST]: building from a list produces a BST
    - [fromList_noRedRed]: building from a list satisfies NoRedRed
    - [findNode_after_insert]: looking up an inserted key finds it
    - [findNode_insert_other]: inserting a different key doesn't affect lookup
*)

(** ** Top-level correctness theorem (scaffold)

    This is the capstone theorem composing all the pieces.
    It will be proven in Phase 7 after all wp proofs are complete. *)

(** For any sequence of key-value pairs, building a tree via [fromList]
    and then looking up a key returns the value from the last insertion
    of that key. This follows from [findNode_after_insert] and
    [findNode_insert_other] in [RBTree.v] by induction on the list. *)

(** ** C++ refinement composition (scaffold)

    When the BRiCk wp proofs are complete, this theorem will compose:
    - C++ insert refines functional insert (InsertSpec.v)
    - C++ findNode refines functional findNode (FindSpec.v)
    - Functional insert preserves BST + NoRedRed (RBTree.v)
    - Reference counting is sound (RefCount.v)

    Into: the C++ Map implementation is a correct, memory-safe BST.

    Top-level C++ correctness:

    {{{ emp }}}
      Map<int,int> m;
      m = m.insert(k1, v1);
      ...
      m = m.insert(kn, vn);
      Node* result = m.findNode(k);
    {{{ ⌜ (result = nullptr ↔ findNode k (fromList [...]) = None) ∧
          (∀ v, findNode k (fromList [...]) = Some v →
                result points to a node with value v) ⌝ }}}
*)
