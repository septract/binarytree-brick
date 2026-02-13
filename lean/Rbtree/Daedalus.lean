import Rbtree.Defs

/-!
# Red-Black Tree Map — Daedalus Implementation

A key-value map implemented as a red-black tree, mirroring the C++ implementation
in [GaloisInc/daedalus `rts-c/ddl/map.h`](https://github.com/GaloisInc/daedalus/blob/master/rts-c/ddl/map.h).

## Structural differences from Classic

The Classic module implements Okasaki's unified `balance` function that handles all four
rotation cases (LL, LR, RL, RR) in a single pattern match. The Daedalus C++ code splits
this into two functions:

- **`setRebalanceLeft`** — handles LL and LR cases (violations in the left subtree)
- **`setRebalanceRight`** — handles RL and RR cases (violations in the right subtree)

This split is a valid refactoring because `ins` only modifies one subtree at a time:
when inserting left, only left violations can arise, so `setRebalanceRight` cases are
unreachable (and vice versa). We prove this equivalence formally in `Daedalus/Proofs.lean`.

## Other differences from Classic

- **Key-value map** (`Tree α β`) rather than a set (`Tree α`).
- **Value update on duplicate keys**: `ins` replaces the value when the key already exists,
  matching the C++ behavior (`n->value = v`).
- **`findNode`**: BST lookup returning `Option β`, mirroring C++ `Node::findNode`.
- **`valid`**: Runtime invariant checker mirroring C++ `Node::valid`.
-/

namespace RBTree.Daedalus

-- ════════════════════════════════════════════════════════════════════════════════
-- Types
-- ════════════════════════════════════════════════════════════════════════════════

/-- Node color. Mirrors `Node::Color` in `map.h` (`red = true`, `black = false`). -/
inductive Color where
  | red
  | black
  deriving Repr, BEq, DecidableEq

/-- A red-black tree storing key-value pairs. Mirrors the `Node` struct in `map.h`.
- `empty` represents a null pointer (conventionally black).
- `node c l k v r` stores color `c`, left subtree `l`, key `k`, value `v`, right subtree `r`. -/
inductive Tree (α β : Type) where
  | empty : Tree α β
  | node : Color → Tree α β → α → β → Tree α β → Tree α β
  deriving Repr

open Color Tree

variable {α β : Type} [Ord α]

-- ════════════════════════════════════════════════════════════════════════════════
-- Color predicates (mirror C++ is_black / is_red)
-- ════════════════════════════════════════════════════════════════════════════════

/-- A tree is black if it is empty or has a black root. Mirrors `Node::is_black`.
Empty trees (null pointers) are considered black. -/
def isBlack : Tree α β → Bool
  | empty => true
  | node black _ _ _ _ => true
  | node red _ _ _ _ => false

/-- A tree is red if it is not black. Mirrors `Node::is_red`. -/
def isRed (t : Tree α β) : Bool := !isBlack t

-- ════════════════════════════════════════════════════════════════════════════════
-- Split rebalancing (mirrors C++ setRebalanceLeft / setRebalanceRight)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Rebalance after inserting into the **left** subtree.

Mirrors `Node::setRebalanceLeft(Node *n, Node *newLeft)` from `map.h`.
The C++ function takes the parent node `n` and the new left child; here we
decompose `n` into its components `(c, _, k, v, r)` since the old left child
is discarded.

Handles two of Okasaki's four rotation cases:
- **LL**: `newLeft = R(R(a,x,b), y, c₁)` — left child's left child is red
- **LR**: `newLeft = R(a, x, R(b,y,c₁))` — left child's right child is red

Both produce the same balanced result: `R(B(a,x,b), y, B(c₁,k,v,r))`. -/
def setRebalanceLeft (c : Color) (newLeft : Tree α β)
    (k : α) (v : β) (r : Tree α β) : Tree α β :=
  match c, newLeft with
  | black, node red (node red a kx vx b) ky vy c₁ =>             -- LL
    node red (node black a kx vx b) ky vy (node black c₁ k v r)
  | black, node red a kx vx (node red b ky vy c₁) =>             -- LR
    node red (node black a kx vx b) ky vy (node black c₁ k v r)
  | c, newLeft =>                                                 -- no violation
    node c newLeft k v r

/-- Rebalance after inserting into the **right** subtree.

Mirrors `Node::setRebalanceRight(Node *n, Node *newRight)` from `map.h`.

Handles two of Okasaki's four rotation cases:
- **RL**: `newRight = R(R(b,y,c₁), z, d)` — right child's left child is red
- **RR**: `newRight = R(b, y, R(c₁,z,d))` — right child's right child is red

Both produce: `R(B(l,k,v,b), y, B(c₁,z,d))`. -/
def setRebalanceRight (c : Color) (l : Tree α β)
    (k : α) (v : β) (newRight : Tree α β) : Tree α β :=
  match c, newRight with
  | black, node red (node red b ky vy c₁) kz vz d =>             -- RL
    node red (node black l k v b) ky vy (node black c₁ kz vz d)
  | black, node red b ky vy (node red c₁ kz vz d) =>             -- RR
    node red (node black l k v b) ky vy (node black c₁ kz vz d)
  | c, newRight =>                                                -- no violation
    node c l k v newRight

-- ════════════════════════════════════════════════════════════════════════════════
-- Reference balance (for equivalence proofs — not present in Daedalus C++)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Okasaki's unified balance function, adapted for key-value trees.

This is **not** part of the Daedalus C++ code. We define it here as a reference
implementation to prove that the split `setRebalanceLeft`/`setRebalanceRight`
is equivalent to unified balancing. The four rotation cases and their result
are identical to `Classic.balance`. -/
def balance (c : Color) (l : Tree α β) (k : α) (v : β) (r : Tree α β) : Tree α β :=
  match c, l, k, v, r with
  | black, node red (node red a kx vx b) ky vy c₁, kz, vz, d =>       -- LL
    node red (node black a kx vx b) ky vy (node black c₁ kz vz d)
  | black, node red a kx vx (node red b ky vy c₁), kz, vz, d =>       -- LR
    node red (node black a kx vx b) ky vy (node black c₁ kz vz d)
  | black, a, kx, vx, node red (node red b ky vy c₁) kz vz d =>       -- RL
    node red (node black a kx vx b) ky vy (node black c₁ kz vz d)
  | black, a, kx, vx, node red b ky vy (node red c₁ kz vz d) =>       -- RR
    node red (node black a kx vx b) ky vy (node black c₁ kz vz d)
  | c, l, k, v, r =>                                                   -- no violation
    node c l k v r

-- ════════════════════════════════════════════════════════════════════════════════
-- Core operations (mirror C++ ins / insert / findNode)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Recursive insert using split rebalancing. Mirrors `Node::ins` from `map.h`.

Unlike `Classic.ins`, this uses `setRebalanceLeft`/`setRebalanceRight` instead
of a unified `balance`, and **updates the value** when the key already exists
(matching the C++ behavior `n->value = v`). -/
def ins (k : α) (v : β) : Tree α β → Tree α β
  | empty => node red empty k v empty
  | node c l kn vn r =>
    match compare k kn with
    | .lt => setRebalanceLeft c (ins k v l) kn vn r
    | .eq => node c l kn v r      -- keep existing key, update value
    | .gt => setRebalanceRight c l kn vn (ins k v r)

/-- Recolor the root to black. Mirrors the assignment `curr->color = black`
in `Node::insert`. -/
def makeBlack : Tree α β → Tree α β
  | node _ l k v r => node black l k v r
  | empty => empty

/-- Insert a key-value pair. Mirrors `Node::insert` from `map.h`:
`ins` then force root black. -/
def insert (k : α) (v : β) (t : Tree α β) : Tree α β :=
  makeBlack (ins k v t)

/-- Look up a key, returning its value if found. Mirrors `Node::findNode` from `map.h`.

The C++ version returns a `Node*` (null if not found); we return `Option β`. -/
def findNode (k : α) : Tree α β → Option β
  | empty => none
  | node _ l kn vn r =>
    match compare k kn with
    | .lt => findNode k l
    | .eq => some vn
    | .gt => findNode k r

-- ════════════════════════════════════════════════════════════════════════════════
-- Validation (mirrors C++ Node::valid)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Check red-black invariants, returning the black-depth on success or 0 on failure.
Mirrors `Node::valid` from `map.h`.

Checks:
1. **No red-red**: no red node has a red child.
2. **Uniform black-depth**: every root-to-empty path has the same number of black nodes. -/
def validAux : Tree α β → Nat
  | empty => 1
  | node c l _ _ r =>
    if c == red && (isRed l || isRed r) then 0
    else
      let ld := validAux l
      let rd := validAux r
      if ld == 0 || ld != rd then 0
      else if c == black then ld + 1 else ld

/-- Is the tree a valid red-black tree? Mirrors the public `Map::valid` from `map.h`. -/
def valid (t : Tree α β) : Bool := validAux t > 0

-- ════════════════════════════════════════════════════════════════════════════════
-- Traversal and construction
-- ════════════════════════════════════════════════════════════════════════════════

/-- In-order traversal producing a sorted list of key-value pairs. -/
def toList : Tree α β → List (α × β)
  | empty => []
  | node _ l k v r => toList l ++ [(k, v)] ++ toList r

/-- Build a tree by left-folding `insert` over a list of key-value pairs. -/
def fromList (kvs : List (α × β)) : Tree α β :=
  kvs.foldl (fun t (k, v) => insert k v t) empty

/-- Number of nodes in the tree. -/
def size : Tree α β → Nat
  | empty => 0
  | node _ l _ _ r => 1 + size l + size r

end RBTree.Daedalus
