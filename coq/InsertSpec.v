(** * Insert Specification and Proof Scaffold

    Proves that the C++ [Node::insert] (and helper [Node::ins],
    [Node::setRebalanceLeft], [Node::setRebalanceRight], [Node::makeCopy])
    refine their functional counterparts from [RBTree.v].

    == C++ functions under verification ==

    - [insert(k, v, n)]: top-level insert, calls [ins] then sets root black
    - [ins(k, v, n)]: recursive insert with ownership transfer + rebalancing
    - [setRebalanceLeft(n, newLeft)]: LL/LR rotation (mutates in place)
    - [setRebalanceRight(n, newRight)]: RL/RR rotation (mutates in place)
    - [makeCopy(p)]: returns unique copy (clone if ref_count > 1, reuse if 1)

    == Key verification challenges ==

    1. **Ownership transfer**: [ins] takes ownership of [k], [v], and [n].
       The separation logic proof must track that each pointer is consumed
       exactly once (either freed, reused, or returned).

    2. **makeCopy**: Forks on [ref_count == 1]. If unique, returns [p]
       unchanged. If shared, allocates a new node (deep copy of fields,
       bumps children's ref counts) and decrements [p]'s ref count.
       The proof must show both branches produce a unique node representing
       the same abstract value.

    3. **In-place mutation**: After [makeCopy] ensures uniqueness, [ins]
       and the rebalance functions mutate fields directly ([n->left = ...]).
       The proof must show these mutations correspond to functional tree
       construction.

    4. **Pointer rotations**: The rebalance functions rearrange pointers
       between three nodes. The proof must track that all intermediate
       states maintain the [tree_rep] invariant.

    == Proof strategy ==

    Bottom-up:
    1. [makeCopy_spec]: produces a unique node with same abstract content
    2. [setRebalanceLeft_spec] / [setRebalanceRight_spec]: rotation correctness
    3. [ins_spec]: recursive correctness (by structural induction on depth)
    4. [insert_spec]: composition of [ins_spec] + [makeBlack]

    == Phase 5 TODO ==

    After Phase 4 (FindSpec.v), fill in BRiCk wp proofs for each function.
*)

From Coq Require Import ZArith Bool Lia.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.

(** ** Functional correctness lemmas *)

(** [ins] into a BST produces a BST. Ported from Lean [isBST_ins]. *)
Lemma isBST_ins : forall k v t,
  IsBST t -> IsBST (ins k v t).
Proof.
  (* Port from Lean: induction on t, case split on comparisons,
     apply isBST_setRebalanceLeft / isBST_setRebalanceRight *)
Admitted.

(** [insert] preserves BST. Ported from Lean [isBST_insert]. *)
Lemma isBST_insert : forall k v t,
  IsBST t -> IsBST (insert k v t).
Proof.
  intros k v t H.
  unfold insert.
  (* makeBlack preserves BST *)
Admitted.

(** [ins] preserves NoRedRed (nearly). Ported from Lean [ins_noRedRed]. *)
Lemma ins_nearly_noRedRed : forall k v t,
  NoRedRed t ->
  (* NearlyNoRedRed (ins k v t) -- children satisfy NoRedRed *)
  match ins k v t with
  | Leaf => True
  | Node _ l _ _ r => NoRedRed l /\ NoRedRed r
  end.
Proof.
Admitted.

(** [insert] preserves NoRedRed. Ported from Lean [noRedRed_insert]. *)
Lemma noRedRed_insert : forall k v t,
  NoRedRed t -> NoRedRed (insert k v t).
Proof.
Admitted.

(** [setRebalanceLeft] equals [balance] when the right subtree has no
    red-red violation. Ported from Lean [setRebalanceLeft_eq_balance]. *)
Lemma setRebalanceLeft_correct : forall c newLeft k v r,
  NoRedRedChildren r ->
  exists t', setRebalanceLeft c newLeft k v r = t' /\
  (* The result is a valid rearrangement of the inputs *)
  True. (* TODO: state precise postcondition *)
Proof.
Admitted.

(** [setRebalanceRight] equals [balance] when the left subtree has no
    red-red violation. Ported from Lean [setRebalanceRight_eq_balance]. *)
Lemma setRebalanceRight_correct : forall c l k v newRight,
  NoRedRedChildren l ->
  exists t', setRebalanceRight c l k v newRight = t' /\
  True. (* TODO: state precise postcondition *)
Proof.
Admitted.

(** ** Hoare triple specifications (scaffold) *)

(** makeCopy specification:

    {{{ tree_rep t p ** ⌜ref_count(p) >= 1⌝ }}}
      makeCopy(p)
    {{{ p', tree_rep t p' ** ⌜ref_count(p') = 1⌝ }}}

    Postcondition: the returned pointer [p'] represents the same abstract
    tree [t] but is guaranteed unique (ref_count = 1). If [p] was already
    unique, [p' = p]. Otherwise, [p'] is freshly allocated.
*)

(** ins specification:

    {{{ tree_rep t p }}}
      ins(k, v, p)
    {{{ p', tree_rep (ins k v t) p' ** ⌜ref_count(p') = 1⌝ }}}

    Consumes ownership of [k], [v], and [p]. Returns a unique node.
*)

(** insert specification:

    {{{ tree_rep t p }}}
      insert(k, v, p)
    {{{ p', tree_rep (insert k v t) p' ** ⌜is_black_root(p')⌝ }}}

    Consumes ownership of [k], [v], and [p]. Returns a tree with a
    black root (enforced by [makeBlack]).
*)

(** setRebalanceLeft specification:

    {{{ tree_rep (Node c old_left k v r) p **
        tree_rep newLeft_abstract pl **
        ⌜ref_count(p) = 1 /\ ref_count(pl) = 1⌝ }}}
      setRebalanceLeft(p, pl)
    {{{ p', tree_rep (setRebalanceLeft c newLeft_abstract k v r) p' **
            ⌜ref_count(p') = 1⌝ }}}
*)
