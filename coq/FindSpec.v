(** * FindNode Specification and Proof Scaffold

    Proves that the C++ [Node::findNode] function refines the functional
    [findNode] from [RBTree.v].

    [findNode] is the simplest operation to verify: it is read-only
    (no allocation, no mutation), making it an ideal warm-up for BRiCk's
    weakest-precondition calculus.

    == C++ function under verification ==

    [[[
    static Node* findNode(Key k, Node *n) {
      Node *curr = n;
      while (curr != nullptr) {
        if (k < curr->key)        curr = curr->left;
        else if (curr->key < k)   curr = curr->right;
        else return curr;
      }
      return nullptr;
    }
    ]]]

    == Proof strategy ==

    The C++ version uses a while loop; the Coq spec uses structural
    recursion. We prove equivalence via a loop invariant:

      I(curr, t_curr) :=
        tree_rep t_orig p_orig **
        findNode k t_orig = findNode k t_curr /\
        tree_rep t_curr curr

    where [t_curr] is the subtree rooted at [curr]. Since [findNode] is
    read-only (borrowing [n]), the full tree representation is preserved
    as a frame throughout the loop.

    == Phase 4 TODO ==

    After Phase 3 (TreeRep.v), fill in:
    1. Import BRiCk wp tactics and generated AST names
    2. State the Hoare triple for findNode
    3. Apply [wp_while] with the loop invariant
    4. Discharge each loop body step using [wp_if], [wp_load], etc.
*)

From Coq Require Import ZArith Bool Lia.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.

(** ** Functional correctness lemmas for [findNode]

    These are pure (non-separation-logic) facts that will be composed
    with the BRiCk wp proof. *)

(** [findNode] respects BST ordering: if the key is found, it equals
    the node's key. *)
Lemma findNode_found_eq : forall k t v,
  findNode k t = Some v ->
  IsBST t ->
  exists l r c, t = Node c l k v r \/
    (exists kn, findNode k (Node c l kn v r) = Some v).
Proof.
  (* Structural induction on the tree, case-splitting on comparisons *)
Admitted.

(** [findNode] on [Leaf] always returns [None]. *)
Lemma findNode_leaf : forall k, findNode k Leaf = None.
Proof. reflexivity. Qed.

(** If [k < kn], [findNode] recurses left. *)
Lemma findNode_lt : forall k c l kn vn r,
  (k < kn)%Z ->
  findNode k (Node c l kn vn r) = findNode k l.
Proof.
  intros. simpl. rewrite Z.ltb_lt in H. rewrite H. reflexivity.
Qed.

(** If [kn < k], [findNode] recurses right. *)
Lemma findNode_gt : forall k c l kn vn r,
  (kn < k)%Z ->
  findNode k (Node c l kn vn r) = findNode k r.
Proof.
  intros. simpl.
  destruct (k <? kn)%Z eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - rewrite Z.ltb_lt in H. rewrite H. reflexivity.
Qed.

(** If [k = kn], [findNode] returns the value. *)
Lemma findNode_eq : forall k c l vn r,
  findNode k (Node c l k vn r) = Some vn.
Proof.
  intros. simpl.
  destruct (k <? k)%Z eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - destruct (k <? k)%Z eqn:Hgt.
    + apply Z.ltb_lt in Hgt. lia.
    + reflexivity.
Qed.

(** ** Hoare triple for findNode (scaffold)

    The specification states: given a tree [t] at pointer [p] satisfying
    [IsBST], calling [findNode(k, p)] returns a result consistent with
    the functional [findNode k t], and the tree is unchanged (read-only). *)

(** Specification (to be stated as a BRiCk wp goal):

    {{{ tree_rep t p }}}
      findNode(k, p)
    {{{ ret,
        tree_rep t p **
        ⌜ (ret = nullptr <-> findNode k t = None) /\
          (forall v, findNode k t = Some v -> ret points to node with value v) ⌝
    }}}
*)

(** Proof outline:
    1. Unfold findNode's while loop using [wp_while]
    2. Loop invariant: [tree_rep t p ** ⌜findNode k t = findNode k t_curr⌝]
    3. Each iteration: [wp_if] on [k < curr->key], [wp_load] for field access
    4. Termination: [curr = nullptr] implies [findNode k t_curr = None]
    5. Found: [k = curr->key] implies [findNode k t_curr = Some curr->value]
*)
