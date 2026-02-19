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

    We use Iris ghost state (a custom CMRA) to track ownership tokens.
    Each allocated node has an associated ghost name [γ] and a token
    resource [own_token γ].

    Invariants:

    - [ref_inv γ p n]: "node [p] has physical ref_count = [n], and
      there are exactly [n] ownership tokens [own_token γ] in
      circulation."  This is an Iris invariant (in [iProp]).

    - [copy(p)] produces a new token:
        [own_token γ ={⊤}=∗ own_token γ ∗ own_token γ]
      (ref_count is bumped by 1).

    - [free(p)] consumes one token:
        If ref_count was 1 (last token): node is deallocated,
        children's tokens are returned.
        If ref_count > 1: ref_count is decremented.

    - [makeCopy(p)] consumes [own_token γ_old] and produces
      [own_token γ_new] where the new node has ref_count = 1.

    == Phase 6 TODO ==

    After Phase 5 (InsertSpec.v):
    1. Define the ghost state CMRA (e.g., [Auth (Excl nat)])
    2. Define [ref_inv] as an Iris invariant using [treeR] and ghost state
    3. Prove [copy_spec], [free_spec], [makeCopy_spec]
    4. Prove key lemma: [insert] produces no leaks (unique ownership out)
    5. Prove key lemma: [free] on a unique tree deallocates everything
*)

From Stdlib Require Import ZArith.

Require Import skylabs.lang.cpp.cpp.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.

Section with_Sigma.
Context `{Sigma : cpp_logic} {CU : genv}.

(** ** Hoare triple specifications

    These require Iris ghost state definitions. The ghost state CMRA
    and [ref_inv] invariant will be defined here once the basic
    operation proofs (FindSpec, InsertSpec) are complete. *)

(** *** copy

    {{{ p |-> treeR q t ** ref_inv γ p n }}}
      Node::copy(p)
    {{{ p |-> treeR q t ** ref_inv γ p (S n) **
        own_token γ }}}

    Produces a new ownership token. The ref_count is incremented. *)

(** *** free

    {{{ own_token γ ** ref_inv γ p n }}}
      Node::free(p)
    {{{ if n = 1:
          (* Last reference: node is deallocated *)
          children's tokens returned, node freed
        else:
          (* Not last: just decrement *)
          ref_inv γ p (n-1) }}} *)

(** *** makeCopy (ghost state version)

    {{{ own_token γ_old ** p |-> treeR 1 t }}}
      makeCopy(p)
    {{{ p', own_token γ_new ** p' |-> treeR 1 t }}}

    Consumes one token for [p], produces a unique token for [p'].
    If [p] was already unique (ref_count = 1), then [p' = p] and
    [γ_new = γ_old]. Otherwise, [p'] is a fresh allocation. *)

(** ** Key composition lemma

    After [insert(k, v, p)], the returned tree has consistent
    ref_count structure: the root has ref_count = 1 (unique ownership
    from the caller's perspective), and shared subtrees from the
    original tree have correctly adjusted ref_counts.

    This composes [ins_spec] (from InsertSpec.v) with [makeCopy_spec]
    to show the overall reference counting discipline is sound. *)

End with_Sigma.
