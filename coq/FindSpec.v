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
    recursion. We prove equivalence via a loop invariant and
    [wp_while_inv] with Löb induction.

    Loop invariant [I(curr)]:
      n |-> treeR q t **
      [| findNode k t = findNode k t_curr |]

    where [t_curr] is the subtree rooted at [curr]. Since [findNode] is
    read-only (borrowing via fractional permission [q]), the full tree
    representation is preserved as a frame throughout the loop.

    Each iteration steps through:
    1. [Sif]: compare [k] vs [curr->key] (two [Ebinop Blt] checks)
    2. [Emember]: load [curr->left] or [curr->right]
    3. Update [curr], re-establish invariant using [findNode_lt]/[findNode_gt]
    4. Termination: [curr = nullptr] ⟹ [findNode k t_curr = None]
    5. Found: [k = curr->key] ⟹ return [curr]

    == Dependencies ==

    Functional correctness lemmas are in [RBTree.v] (zero [Admitted]).
    This file keeps only the directional lemmas [findNode_lt] and
    [findNode_gt] which are convenient for the loop proof steps.
*)

From Coq Require Import ZArith Bool Lia.

Require Import daedalus_rb.RBTree.

(** ** Directional recursion lemmas

    These characterize [findNode]'s branching behavior and are used
    directly in the loop body proof to re-establish the invariant.

    Proven before BRiCk imports to avoid ssreflect [rewrite] conflict. *)

(** If [k < kn], [findNode] recurses left. *)
Lemma findNode_lt : forall k c l kn vn r,
  (k < kn)%Z ->
  findNode k (Node c l kn vn r) = findNode k l.
Proof.
  intros k c l kn vn r Hlt. simpl.
  destruct (k <? kn)%Z eqn:E; [reflexivity |].
  apply Z.ltb_ge in E. lia.
Qed.

(** If [kn < k], [findNode] recurses right. *)
Lemma findNode_gt : forall k c l kn vn r,
  (kn < k)%Z ->
  findNode k (Node c l kn vn r) = findNode k r.
Proof.
  intros k c l kn vn r Hgt. simpl.
  destruct (k <? kn)%Z eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (kn <? k)%Z eqn:E2; [reflexivity |].
    apply Z.ltb_ge in E2. lia.
Qed.

(** ** BRiCk imports (after pure lemmas to avoid ssreflect conflicts) *)

Require Import skylabs.lang.cpp.cpp.
Import cQp_compat.

Require Import daedalus_rb.TreeRep.

(** ** BRiCk function specification

    [findNode_spec] is the separation logic specification for the C++
    [DDL::Map<int,int>::Node::findNode] static method.

    Type: [static Node* findNode(int k, Node* n)]

    The spec uses fractional permission [q] (read-only access via the
    [borrow_from] pattern):

    - **Pre**: the tree [t] is represented at pointer [p] with permission [q]
    - **Post**: the tree is unchanged; the return value is consistent with
      the functional [findNode k t]:
      - [nullptr] when [findNode k t = None]
      - a non-null pointer to a node with the found value otherwise

    The specification follows BRiCk's [SFunction] pattern for static
    methods (cf. [count_spec] in [howto_sequential.v]).

    {{{ p |-> treeR q t }}}
      findNode(k, p)
    {{{ ret,
        p |-> treeR q t **
        ⌜ match findNode k t with
          | None   => ret = Vptr nullptr
          | Some _ => ret <> Vptr nullptr
          end ⌝
    }}}
*)

Section with_Sigma.
Context `{Sigma : cpp_logic} {CU : genv}.

(** The C++ function specification.

    [findNode] is a static method, so both arguments are explicit.
    The tree is borrowed (fractional [q]) via [\prepost] — it is
    unchanged across the call.  The return value is a [Node*]:
    [nullptr] when the key is absent, non-null when present.

    Pattern follows [count_spec] / [insert_spec] from
    [howto_sequential.v]. *)

Definition findNode_spec :=
  cpp_spec (Tptr _Node) (Tint :: Tptr _Node :: nil) $
    \with (q : Qp) (t : tree Z Z)
    \arg{k} "k" (Vint k)
    \arg{n} "n" (Vptr n)
    \prepost n |-> treeR q t
    \post{ret}[Vptr ret]
      [| match findNode k t with
         | None   => ret = nullptr
         | Some _ => ret <> nullptr
         end |].

End with_Sigma.

(** ** Proof outline

    The wp proof will use:

    1. [wp_while_inv] with Löb induction over the loop body
    2. Loop invariant binds [curr : ptr] and ghost [t_curr : tree Z Z]:
       [p |-> treeR q t ** [| findNode k t = findNode k t_curr |]]
    3. Each branch of the [Sif] (the [k < curr->key] and [curr->key < k]
       comparisons) uses [wp_load] to read [curr->key], then
       [findNode_lt] or [findNode_gt] to re-establish the invariant
    4. The [else return curr] branch uses [findNode_eq] from [RBTree.v]
    5. Loop exit ([curr = nullptr]) uses [treeR_leaf] from [TreeRep.v]
       to conclude [findNode k t_curr = None]

    The frame rule preserves [p |-> treeR q t] since [findNode] only
    reads the tree (fractional permission [q]).
*)
