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
       states maintain the [treeR] invariant.

    == Proof strategy ==

    Bottom-up:
    1. [makeCopy_spec]: produces a unique node with same abstract content
    2. [setRebalanceLeft_spec] / [setRebalanceRight_spec]: rotation correctness
    3. [ins_spec]: recursive correctness (by structural induction on depth)
    4. [insert_spec]: composition of [ins_spec] + [makeBlack]

    All functional correctness lemmas ([isBST_ins], [isBST_insert],
    [noRedRed_insert], etc.) are proven in [RBTree.v] with zero [Admitted].
    This file contains only the BRiCk separation logic specifications.

    == Phase 5 TODO ==

    After Phase 4 (FindSpec.v), fill in BRiCk wp proofs for each function.
*)

From Coq Require Import ZArith Bool Lia.

Require Import skylabs.lang.cpp.cpp.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.

Section with_Sigma.
Context `{Sigma : cpp_logic} {CU : genv}.

(** ** Hoare triple specifications

    Each spec follows BRiCk's [SFunction] / [SMethod] pattern.
    The proofs require the cpp2v-generated AST ([map_int_int_cpp.v]). *)

(** *** makeCopy

    {{{ this |-> treeR 1 t }}}
      makeCopy(this)
    {{{ p', p' |-> treeR 1 t }}}

    Consumes the input pointer. Returns a pointer with exclusive
    ownership (ref_count = 1). If the input was already unique
    (ref_count = 1), returns the same pointer. Otherwise, allocates
    a fresh deep copy and decrements the original's ref_count. *)

(** *** setRebalanceLeft

    {{{ this |-> treeR 1 (Node c old_left k v r) **
        pl |-> treeR 1 newLeft }}}
      setRebalanceLeft(this, pl)
    {{{ this |-> treeR 1 (setRebalanceLeft c newLeft k v r) }}}

    Mutates [this] in place: replaces [old_left] with [newLeft] and
    performs LL/LR rotation if needed. Consumes [pl]. *)

(** *** setRebalanceRight (symmetric) *)

(** *** ins

    {{{ p |-> treeR 1 t }}}
      ins(k, v, p)
    {{{ p', p' |-> treeR 1 (ins k v t) }}}

    Recursive insert. Takes exclusive ownership of [p], returns
    exclusive ownership of the result. Uses [makeCopy] internally
    to ensure uniqueness before mutation. *)

(** *** insert

    {{{ p |-> treeR 1 t }}}
      insert(k, v, p)
    {{{ p', p' |-> treeR 1 (insert k v t) }}}

    Top-level insert: calls [ins] then forces root black.
    The returned tree satisfies [IsBST] and [NoRedRed] if the
    input did (proven in [RBTree.v]). *)

End with_Sigma.
