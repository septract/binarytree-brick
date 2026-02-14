(** * Reference Counting Correctness

    Proves that the C++ reference counting discipline in [DDL::Map<int,int>]
    is sound: every allocated node is eventually freed, and no node is
    used after being freed.

    == C++ functions under verification ==

    - [Node::copy(Node* n)]: increments ref_count (if non-null)
    - [Node::free(Node* n)]: decrements ref_count; if it reaches 0,
      recursively frees children and deallocates
    - [Node(Node* n)]: copy constructor — clones fields, bumps children's
      ref counts
    - [makeCopy(Node* p)]: returns unique copy (reuse if ref_count=1,
      clone otherwise)

    == Proof strategy: Iris ghost state ==

    We use Iris fractional permissions (or a custom ghost state) to track
    ownership tokens:

    - [own_token p] represents one unit of ownership of node [p].
      A node with ref_count = n has exactly n tokens outstanding.
    - [copy(p)] produces a new token: [own_token p] ~~> [own_token p ** own_token p]
      (conceptually; the ref_count is bumped by 1).
    - [free(p)] consumes one token. If it was the last token (ref_count
      was 1), the node is deallocated and children's tokens are consumed.
    - [makeCopy(p)] consumes [own_token p] and produces [own_token p']
      where [p'] has ref_count = 1 (unique ownership).

    == Phase 6 TODO ==

    After Phase 5 (InsertSpec.v), implement using Iris ghost state:
    1. Define the ghost state CMRA for ownership tokens
    2. Define [ref_inv p n]: "node [p] has ref_count [n] and there are
       [n] tokens for [p] in circulation"
    3. Prove [copy_spec], [free_spec], [makeCopy_spec]
*)

From Coq Require Import ZArith.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.

(** ** Ownership token (scaffold)

    In the full Iris proof, this would be a ghost resource.
    For now, we define it at the Prop level. *)

(** An ownership token for a node at address [p].
    In the real proof, this is an Iris ghost assertion. *)
Definition own_token (p : val) : Prop := p <> 0%Z.  (* PLACEHOLDER *)

(** ** Reference count invariant (scaffold)

    Links the physical ref_count field to the number of outstanding tokens. *)

(** [ref_inv p n] asserts: node [p] has ref_count = [n], and there are
    exactly [n] ownership tokens for [p] in circulation.

    This is the key invariant maintained by copy/free. *)
Definition ref_inv (p : val) (n : nat) : Prop :=
  p <> 0%Z /\ n >= 1.  (* PLACEHOLDER: real version uses ghost state *)

(** ** Specification scaffolds *)

(** copy specification:

    {{{ own_token p ** ref_inv p n }}}
      Node::copy(p)
    {{{ own_token p ** own_token p ** ref_inv p (S n) }}}

    Produces a new token. The ref_count is incremented. *)

(** free specification:

    {{{ own_token p ** ref_inv p n }}}
      Node::free(p)
    {{{ if n = 1:
          (* Last reference: node is deallocated *)
          own_token(left) ** own_token(right) ** freed(p)
        else:
          (* Not last: just decrement *)
          ref_inv p (n-1) }}}

    Consumes one token. If last, deallocates and yields children's tokens. *)

(** makeCopy specification:

    {{{ own_token p ** tree_rep t p }}}
      makeCopy(p)
    {{{ p', own_token p' ** tree_rep t p' ** ⌜ref_count(p') = 1⌝ }}}

    Consumes one token for [p], produces a unique token for [p'].
    If [p] was already unique (ref_count = 1), then [p' = p].
    Otherwise, [p'] is a fresh allocation. *)

(** ** Key lemma: insert produces no leaks

    After [insert(k, v, p)], the returned tree's ref_count structure
    is consistent: every internal node has ref_count = 1 (unique
    ownership from the caller's perspective), and any shared subtrees
    from the original tree have their ref_counts correctly adjusted. *)
Lemma insert_no_leak : forall k v t p,
  (* Assuming well-formed initial tree *)
  tree_rep_spec t p ->
  (* insert consumes ownership of p and produces a new tree *)
  True.  (* PLACEHOLDER: full statement requires ghost state *)
Proof.
Admitted.

(** ** Key lemma: free deallocates the entire tree

    [free(p)] on a tree where every node has ref_count = 1
    deallocates every node. *)
Lemma free_unique_tree : forall t p,
  tree_rep_spec t p ->
  (* All nodes have ref_count = 1 *)
  (* After free(p), all nodes are deallocated *)
  True.  (* PLACEHOLDER *)
Proof.
Admitted.
