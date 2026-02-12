/-
  Red-Black Tree with Double-Black deletion (Matt Might's approach).

  Extends the classic 2-color Red-Black Tree with transient colors
  (double-black, negative-black) to support functional deletion.

  The deletion algorithm has three phases:
  1. Remove: delete the target node, possibly creating a double-black marker
  2. Bubble: propagate double-black upward via color arithmetic
  3. Balance: eliminate negative-black violations via rotation

  Reference: Matt Might, "Deletion: The curse of the red-black tree"
  https://matt.might.net/articles/red-black-delete/
-/

import Rbtree.Defs

namespace RBTree.DoubleBlack

/-- Extended node color with transient markers for deletion. -/
inductive Color where
  | red
  | black
  | doubleBlack    -- transient: counts as 2 for black-height
  | negativeBlack  -- transient: counts as -1 for black-height
  deriving Repr, BEq, DecidableEq

/-- A red-black tree with double-black leaf support. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | doubleBlackLeaf : Tree α
  | node : Color → Tree α → α → Tree α → Tree α
  deriving Repr

open Color Tree

variable {α : Type} [Ord α]

-- ══════════════════════════════════════════════════════════════════════
-- Color arithmetic
-- ══════════════════════════════════════════════════════════════════════

/-- Increment the black level of a color ("black + 1"). -/
def Color.incBlack : Color → Color
  | negativeBlack => red
  | red           => black
  | black         => doubleBlack
  | doubleBlack   => doubleBlack  -- saturate

/-- Decrement the black level of a color ("black - 1"). -/
def Color.decBlack : Color → Color
  | doubleBlack   => black
  | black         => red
  | red           => negativeBlack
  | negativeBlack => negativeBlack  -- saturate

/-- Decrement the black level of a tree node ("black - 1" on a tree). -/
def Tree.decBlack : Tree α → Tree α
  | doubleBlackLeaf => leaf
  | node c l v r    => node c.decBlack l v r
  | leaf            => leaf  -- shouldn't arise in practice

-- ══════════════════════════════════════════════════════════════════════
-- Core operations
-- ══════════════════════════════════════════════════════════════════════

/-- Test whether a value is in the tree. -/
def contains (x : α) : Tree α → Bool
  | leaf => false
  | doubleBlackLeaf => false
  | node _ l v r =>
    match compare x v with
    | .lt => contains x l
    | .eq => true
    | .gt => contains x r

/-- Core balance: fix red-red violations (Okasaki's 4 rotation cases).
    This is non-recursive and handles only the standard insertion violations. -/
def balanceCore (color : Color) (l : Tree α) (v : α) (r : Tree α) : Tree α :=
  match color, l, v, r with
  | black, node red (node red a x b) y c₁, z, d =>         -- LL
    node red (node black a x b) y (node black c₁ z d)
  | black, node red a x (node red b y c₁), z, d =>         -- LR
    node red (node black a x b) y (node black c₁ z d)
  | black, a, x, node red (node red b y c₁) z d =>         -- RL
    node red (node black a x b) y (node black c₁ z d)
  | black, a, x, node red b y (node red c₁ z d) =>         -- RR
    node red (node black a x b) y (node black c₁ z d)
  | color, l, v, r =>                                       -- no violation
    node color l v r

/-- Extended balance: handles both red-red violations and negative-black elimination.
    Cases 1-4 (red-red) are delegated to `balanceCore`.
    Cases 5-6 (negative-black) arise only during deletion and call `balanceCore`
    internally — since the inner call always has `c = black`, it can only trigger
    the red-red cases, never recurse back into the NB cases. -/
def balance (color : Color) (l : Tree α) (v : α) (r : Tree α) : Tree α :=
  match color, l, v, r with
  -- Case 5: Double-black parent, negative-black left child
  | doubleBlack, node negativeBlack (node black a w b) x s, y, node black d z e =>
    node black (balanceCore black (node red a w b) x s) y (node black d z e)
  -- Case 6: Double-black parent, negative-black right child (symmetric)
  | doubleBlack, node black a w b, x, node negativeBlack s y (node black d z e) =>
    node black (node black a w b) x (balanceCore black s y (node red d z e))
  -- All other cases: delegate to core balance
  | color, l, v, r => balanceCore color l v r

/-- Insert into the tree (internal: may produce a red root). -/
def ins (x : α) : Tree α → Tree α
  | leaf => node red leaf x leaf
  | doubleBlackLeaf => node red leaf x leaf  -- shouldn't arise in valid trees
  | node c l v r =>
    match compare x v with
    | .lt => balance c (ins x l) v r
    | .eq => node c l v r
    | .gt => balance c l v (ins x r)

/-- Force the root to black. Also eliminates a double-black root or leaf. -/
def makeBlack : Tree α → Tree α
  | node _ l v r => node black l v r
  | doubleBlackLeaf => leaf
  | leaf => leaf

/-- Insert a value into the red-black tree. -/
def insert (x : α) (t : Tree α) : Tree α :=
  makeBlack (ins x t)

/-- In-order traversal producing a sorted list. -/
def toList : Tree α → List α
  | leaf => []
  | doubleBlackLeaf => []
  | node _ l v r => toList l ++ [v] ++ toList r

/-- Build a tree from a list of values. -/
def fromList (xs : List α) : Tree α :=
  xs.foldl (fun t x => insert x t) leaf

/-- Number of elements in the tree. -/
def size : Tree α → Nat
  | leaf => 0
  | doubleBlackLeaf => 0
  | node _ l _ r => 1 + size l + size r

/-- Height of the tree. -/
def height : Tree α → Nat
  | leaf => 0
  | doubleBlackLeaf => 0
  | node _ l _ r => 1 + max (height l) (height r)

/-- Count the black height (along the leftmost path). -/
def blackHeight : Tree α → Nat
  | leaf => 1
  | doubleBlackLeaf => 2
  | node c l _ _ =>
    (match c with
     | black => 1
     | doubleBlack => 2
     | red => 0
     | negativeBlack => 0) + blackHeight l

-- ══════════════════════════════════════════════════════════════════════
-- Deletion
-- ══════════════════════════════════════════════════════════════════════

/-- Check if a tree node is double-black (transient deficit marker). -/
def isDoubleBlack : Tree α → Bool
  | doubleBlackLeaf      => true
  | node doubleBlack .. => true
  | _                    => false

/-- Propagate double-black upward via color arithmetic.
    If either child is double-black, increment the parent's black level
    and decrement both children's, then rebalance. -/
def bubble (c : Color) (l : Tree α) (v : α) (r : Tree α) : Tree α :=
  if isDoubleBlack l || isDoubleBlack r then
    balance c.incBlack l.decBlack v r.decBlack
  else
    node c l v r

/-- Remove the maximum element from a non-empty tree.
    Returns `none` on leaf/doubleBlackLeaf (caller ensures this doesn't happen). -/
def removeMax : Tree α → Option (α × Tree α)
  | node c l v leaf =>
    some (v, match c, l with
      | black, leaf          => doubleBlackLeaf
      | black, _             => makeBlack l
      | _, _                 => l)
  | node c l v r =>
    match removeMax r with
    | some (m, r') => some (m, bubble c l v r')
    | none         => some (v, l)  -- shouldn't happen: r is non-leaf in this branch
  | leaf => none
  | doubleBlackLeaf => none

/-- Internal delete (may produce a double-black root). -/
def del (x : α) : Tree α → Tree α
  | leaf => leaf
  | doubleBlackLeaf => doubleBlackLeaf
  | node c l v r =>
    match compare x v with
    | .lt => bubble c (del x l) v r
    | .gt => bubble c l v (del x r)
    | .eq =>
      match l, r with
      | leaf, leaf =>
        if c == black then doubleBlackLeaf else leaf
      | leaf, _ =>
        if c == black then makeBlack r else r
      | _, leaf =>
        if c == black then makeBlack l else l
      | _, _ =>
        match removeMax l with
        | some (pred, l') => bubble c l' pred r
        | none            => node c l v r  -- unreachable: l is non-leaf

/-- Delete a value from the red-black tree. -/
def delete (x : α) (t : Tree α) : Tree α :=
  makeBlack (del x t)

end RBTree.DoubleBlack
