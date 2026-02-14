(** * Functional Specification: Red-Black Tree Map

    Ported from [Rbtree/Daedalus.lean]. This module defines the pure functional
    spec against which we verify the C++ [DDL::Map<int,int>] implementation.

    The C++ code follows Okasaki's red-black tree with split rebalancing:
    [setRebalanceLeft] handles LL/LR cases, [setRebalanceRight] handles RL/RR.
    We mirror that structure here rather than using unified [balance].

    All definitions correspond 1:1 with the Lean formalization. See
    [Rbtree/Daedalus.lean] for the detailed documentation of each definition.
*)

From Coq Require Import ZArith List Bool Lia.
Import ListNotations.

(** ** Types *)

(** Node color. Mirrors [Node::Color] in [map.h]. *)
Inductive Color : Type :=
  | Red : Color
  | Black : Color.

(** A red-black tree storing key-value pairs. Mirrors the [Node] struct.
    - [Leaf] represents a null pointer (conventionally black).
    - [Node c l k v r] stores color, left subtree, key, value, right subtree. *)
Inductive tree (K V : Type) : Type :=
  | Leaf : tree K V
  | Node : Color -> tree K V -> K -> V -> tree K V -> tree K V.

Arguments Leaf {K V}.
Arguments Node {K V}.

(** ** Color predicates *)

(** Mirrors [Node::is_black]: empty trees (null) are black. *)
Definition is_black {K V : Type} (t : tree K V) : bool :=
  match t with
  | Leaf => true
  | Node Black _ _ _ _ => true
  | Node Red _ _ _ _ => false
  end.

(** Mirrors [Node::is_red]. *)
Definition is_red {K V : Type} (t : tree K V) : bool :=
  negb (is_black t).

(** ** Split rebalancing *)

(** Rebalance after inserting into the left subtree.
    Mirrors [Node::setRebalanceLeft] from [map.h].

    Handles LL and LR rotation cases. *)
Definition setRebalanceLeft {K V : Type}
    (c : Color) (newLeft : tree K V) (k : K) (v : V) (r : tree K V)
    : tree K V :=
  match c, newLeft with
  (* LL: left child's left child is red *)
  | Black, Node Red (Node Red a kx vx b) ky vy c1 =>
      Node Red (Node Black a kx vx b) ky vy (Node Black c1 k v r)
  (* LR: left child's right child is red *)
  | Black, Node Red a kx vx (Node Red b ky vy c1) =>
      Node Red (Node Black a kx vx b) ky vy (Node Black c1 k v r)
  (* No violation *)
  | _, _ =>
      Node c newLeft k v r
  end.

(** Rebalance after inserting into the right subtree.
    Mirrors [Node::setRebalanceRight] from [map.h].

    Handles RL and RR rotation cases. *)
Definition setRebalanceRight {K V : Type}
    (c : Color) (l : tree K V) (k : K) (v : V) (newRight : tree K V)
    : tree K V :=
  match c, newRight with
  (* RL: right child's left child is red *)
  | Black, Node Red (Node Red b ky vy c1) kz vz d =>
      Node Red (Node Black l k v b) ky vy (Node Black c1 kz vz d)
  (* RR: right child's right child is red *)
  | Black, Node Red b ky vy (Node Red c1 kz vz d) =>
      Node Red (Node Black l k v b) ky vy (Node Black c1 kz vz d)
  (* No violation *)
  | _, _ =>
      Node c l k v newRight
  end.

(** ** Core operations *)

(** Recursive insert with split rebalancing. Mirrors [Node::ins].

    Unlike Okasaki's unified [balance], uses [setRebalanceLeft] and
    [setRebalanceRight]. Updates the value when the key already exists,
    matching the C++ behavior [n->value = v]. *)
Fixpoint ins (k : Z) (v : Z) (t : tree Z Z) : tree Z Z :=
  match t with
  | Leaf => Node Red Leaf k v Leaf
  | Node c l kn vn r =>
      if (k <? kn)%Z then
        setRebalanceLeft c (ins k v l) kn vn r
      else if (kn <? k)%Z then
        setRebalanceRight c l kn vn (ins k v r)
      else
        (* k = kn: update value, keep key *)
        Node c l kn v r
  end.

(** Force root to black. Mirrors [curr->color = black] in [Node::insert]. *)
Definition makeBlack {K V : Type} (t : tree K V) : tree K V :=
  match t with
  | Node _ l k v r => Node Black l k v r
  | Leaf => Leaf
  end.

(** Top-level insert: [ins] then force root black. Mirrors [Node::insert]. *)
Definition insert (k : Z) (v : Z) (t : tree Z Z) : tree Z Z :=
  makeBlack (ins k v t).

(** Lookup a key, returning its value if found.
    Mirrors [Node::findNode] (which returns a Node pointer; we return option). *)
Fixpoint findNode (k : Z) (t : tree Z Z) : option Z :=
  match t with
  | Leaf => None
  | Node _ l kn vn r =>
      if (k <? kn)%Z then findNode k l
      else if (kn <? k)%Z then findNode k r
      else Some vn
  end.

(** ** Invariants *)

(** Every key in the tree satisfies predicate [p]. *)
Fixpoint ForAll {K V : Type} (p : K -> Prop) (t : tree K V) : Prop :=
  match t with
  | Leaf => True
  | Node _ l k _ r => ForAll p l /\ p k /\ ForAll p r
  end.

(** BST ordering invariant on keys. *)
Fixpoint IsBST (t : tree Z Z) : Prop :=
  match t with
  | Leaf => True
  | Node _ l k _ r =>
      IsBST l /\ IsBST r /\
      ForAll (fun x => (x < k)%Z) l /\
      ForAll (fun x => (k < x)%Z) r
  end.

(** No red node has a red child (recursive, whole-tree property). *)
Fixpoint NoRedRed {K V : Type} (t : tree K V) : Prop :=
  match t with
  | Leaf => True
  | Node Red (Node Red _ _ _ _) _ _ _ => False
  | Node Red _ _ _ (Node Red _ _ _ _) => False
  | Node _ l _ _ r => NoRedRed l /\ NoRedRed r
  end.

(** No red-red violation at the top level only. *)
Definition NoRedRedChildren {K V : Type} (t : tree K V) : Prop :=
  match t with
  | Node Red (Node Red _ _ _ _) _ _ _ => False
  | Node Red _ _ _ (Node Red _ _ _ _) => False
  | _ => True
  end.

(** ** Validation *)

Definition Color_eqb (c1 c2 : Color) : bool :=
  match c1, c2 with
  | Red, Red => true
  | Black, Black => true
  | _, _ => false
  end.

(** Runtime invariant checker returning black-depth, 0 on failure.
    Mirrors [Node::valid] from [map.h]. *)
Fixpoint validAux {K V : Type} (t : tree K V) : nat :=
  match t with
  | Leaf => 1
  | Node c l _ _ r =>
      if (andb (Color_eqb c Red) (orb (is_red l) (is_red r)))
      then 0
      else
        let ld := validAux l in
        let rd := validAux r in
        if (orb (Nat.eqb ld 0) (negb (Nat.eqb ld rd)))
        then 0
        else if Color_eqb c Black then S ld else ld
  end.

(** ** Traversal *)

(** In-order traversal producing sorted key-value pairs. *)
Fixpoint toList {K V : Type} (t : tree K V) : list (K * V) :=
  match t with
  | Leaf => nil
  | Node _ l k v r => toList l ++ (k, v) :: toList r
  end.

(** Build a tree by left-folding [insert] over a list. *)
Definition fromList (kvs : list (Z * Z)) : tree Z Z :=
  fold_left (fun t kv => insert (fst kv) (snd kv) t) kvs Leaf.
