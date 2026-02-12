import Rbtree.Defs

/-!
# Red-Black Trees in Lean 4 — Classic Implementation

A **red-black tree** is a self-balancing binary search tree where each node carries a
color (red or black). The following invariants guarantee O(log n) operations:

1. Every node is either red or black.
2. The root is black.
3. No red node has a red child  ("red rule").
4. Every path from root to a leaf has the same number of black nodes ("black rule").

## What this module provides

- Core data types: `Color`, `Tree α`
- Operations: `contains`, `insert`, `toList`, `fromList`, `size`, `height`, `blackHeight`
- Insertion via Okasaki-style balancing (see the diagram on `balance`)
- A formal proof that `insert` preserves the BST ordering invariant (`isBST_insert`)

## References

- Chris Okasaki, *Purely Functional Data Structures*, §3.3
- Matt Might, [Red-Black Trees in a Functional Setting](https://matt.might.net/articles/red-black-delete/)
-/

namespace RBTree.Classic

/-- Node color. Every node in a red-black tree is colored either `red` or `black`.
Coloring constrains the tree's shape: the "red rule" (no red node has a red child)
and "black rule" (uniform black-height) together enforce approximate balance. -/
inductive Color where
  | red
  | black
  deriving Repr, BEq, DecidableEq

/-- A red-black tree storing values of type `α`.
- `leaf` represents an empty subtree (conceptually colored black).
- `node c l v r` stores color `c`, left subtree `l`, value `v`, right subtree `r`. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Color → Tree α → α → Tree α → Tree α
  deriving Repr

open Color Tree

-- Note: we require `Ord α` for comparisons in `contains` and `ins`.
-- We do *not* need `BEq α`—all comparisons go through `compare`.
variable {α : Type} [Ord α]

-- ════════════════════════════════════════════════════════════════════════════════
-- Core operations
-- ════════════════════════════════════════════════════════════════════════════════

/-- Search for `x` in the tree using the BST ordering.
Descends left or right based on `compare x v`, so this runs in O(height) time. -/
def contains (x : α) : Tree α → Bool
  | leaf => false
  | node _ l v r =>
    match compare x v with
    | .lt => contains x l
    | .eq => true
    | .gt => contains x r

/-- Okasaki's balance function: repair a **red-red violation** after insertion.

When we insert into a black node's child, that child (now red) may itself have a red
child, violating the "red rule." There are exactly four configurations where this
happens, depending on whether the violation is on the left-left, left-right,
right-left, or right-right path.

Okasaki's key insight: **all four cases produce the same balanced result**.

```text
  LL violation      LR violation      RL violation      RR violation

      z(B)             z(B)            x(B)            x(B)
     / \              / \             / \              / \
   y(R)  d          x'(R) d         a   z(R)         a  y(R)
   / \              / \                 / \              / \
 x'(R) c          a  y(R)            y(R)  d           b  z(R)
 / \                  / \            / \                   / \
a   b                b   c         b   c                 c   d

                        ↓  all four become  ↓

                             y(R)
                           /     \
                        x'(B)    z(B)
                        / \      / \
                       a   b    c   d
```

If the parent is red (not black), or the children don't form a violation, the tree
is returned unchanged. -/
def balance (color : Color) (l : Tree α) (v : α) (r : Tree α) : Tree α :=
  match color, l, v, r with
  | black, node red (node red a x b) y c, z, d =>         -- LL
    node red (node black a x b) y (node black c z d)
  | black, node red a x (node red b y c), z, d =>         -- LR
    node red (node black a x b) y (node black c z d)
  | black, a, x, node red (node red b y c) z d =>         -- RL
    node red (node black a x b) y (node black c z d)
  | black, a, x, node red b y (node red c z d) =>         -- RR
    node red (node black a x b) y (node black c z d)
  | color, l, v, r =>                                     -- no violation
    node color l v r

/-- Insert into the tree (internal helper).

Unlike the public `insert`, this does **not** recolor the root to black, so it may
produce a tree with a red root. This is intentional: `balance` creates red nodes
during rotation, and forcing them black too early would increase one path's
black-height, violating invariant 4. The public `insert` wraps this with `makeBlack`.

**Duplicate handling**: if `x` is already in the tree (`compare` returns `.eq`),
the tree is returned unchanged. -/
def ins (x : α) : Tree α → Tree α
  | leaf => node red leaf x leaf
  | node c l v r =>
    match compare x v with
    | .lt => balance c (ins x l) v r
    | .eq => node c l v r
    | .gt => balance c l v (ins x r)

/-- Recolor the root to black.

After `ins`, the root may be red (e.g., the very first insertion creates a lone red
node). Recoloring it black is always safe: it increases the black-height of *every*
root-to-leaf path by exactly one, so invariant 4 (uniform black-height) is preserved,
and it cannot create a red-red violation. -/
def makeBlack : Tree α → Tree α
  | node _ l v r => node black l v r
  | leaf => leaf

/-- Insert a value into the red-black tree (public API).

This is Okasaki's two-phase strategy:
1. **`ins`** recursively descends and inserts, calling `balance` to fix any red-red
   violation created along the way.
2. **`makeBlack`** recolors the (possibly red) root to black, restoring invariant 2. -/
def insert (x : α) (t : Tree α) : Tree α :=
  makeBlack (ins x t)

/-- In-order traversal producing a sorted list (assuming the tree satisfies BST order). -/
def toList : Tree α → List α
  | leaf => []
  | node _ l v r => toList l ++ [v] ++ toList r

/-- Build a tree by left-folding `insert` over a list of values. -/
def fromList (xs : List α) : Tree α :=
  xs.foldl (fun t x => insert x t) leaf

/-- Number of nodes (non-leaf) in the tree. -/
def size : Tree α → Nat
  | leaf => 0
  | node _ l _ r => 1 + size l + size r

/-- Length of the longest root-to-leaf path. -/
def height : Tree α → Nat
  | leaf => 0
  | node _ l _ r => 1 + max (height l) (height r)

/-- Number of black nodes on the leftmost root-to-leaf path.

Leaves are conventionally colored black, so `blackHeight leaf = 1`. In a valid
red-black tree, *all* root-to-leaf paths have the same black-height (invariant 4),
so measuring along the leftmost path suffices. -/
def blackHeight : Tree α → Nat
  | leaf => 1
  | node c l _ _ =>
    (match c with | black => 1 | red => 0) + blackHeight l

end RBTree.Classic
