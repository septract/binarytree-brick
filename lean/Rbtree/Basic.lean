/-!
# Red-Black Trees in Lean 4

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

namespace RBTree

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

-- ════════════════════════════════════════════════════════════════════════════════
-- BST ordering invariant and its preservation by `insert`
-- ════════════════════════════════════════════════════════════════════════════════

/-! ### Defining the BST invariant

We define `ForAll p t` ("every value in `t` satisfies `p`") and `IsBST t` as
**recursive functions returning `Prop`**, rather than as inductive predicates.

This is a deliberate design choice that simplifies the proofs. When we case-split on
`balance` (which has five match arms), the `split` tactic introduces equalities
without substituting them into hypotheses. Recursive function definitions interact
well with `simp` in this setting — `simp [IsBST, ForAll]` can unfold through the
constructors — whereas inductive predicates would require explicit `cases`/`inversion`
on each hypothesis after substitution.

**Note**: The proofs below are restricted to `Nat` for simplicity. They use
`Nat.lt_trans` and `Nat.compare_eq_lt`/`Nat.compare_eq_gt`. Generalizing to an
arbitrary `LinearOrder` would require only swapping these for their generic versions. -/

/-- Every value stored in the tree satisfies predicate `p`.
Defined recursively: trivially true for `leaf`, and for a `node` it requires
`p` to hold for everything in the left subtree, for the node's value, and for
everything in the right subtree. -/
def ForAll (p : α → Prop) : Tree α → Prop
  | leaf => True
  | node _ l v r => ForAll p l ∧ p v ∧ ForAll p r

/-- The BST ordering invariant: for every `node _ l v r`,
- every value in `l` is **less than** `v`, and
- every value in `r` is **greater than** `v`,

recursively throughout the tree. This is what makes `contains` correct. -/
def IsBST : Tree Nat → Prop
  | leaf => True
  | node _ l v r =>
    IsBST l ∧ IsBST r ∧ ForAll (· < v) l ∧ ForAll (v < ·) r

/-! ### Proof architecture

Our goal is to prove `isBST_insert`: inserting into a BST yields a BST.

The proof is structured as a chain of lemmas:

```text
isBST_insert                     -- top-level theorem
 ├── isBST_makeBlack             -- recoloring the root doesn't affect ordering
 └── isBST_ins                   -- the recursive insert preserves IsBST
       ├── isBST_balance          -- the hard part: each rotation preserves IsBST
       ├── forAll_lt_ins          -- ins into a "< v" tree stays "< v"
       └── forAll_gt_ins          -- ins into a "> v" tree stays "> v"
             ├── forAll_balance   -- ForAll distributes through balance
             ├── forAll_lt_weaken -- bound weakening: (∀ x ∈ t, x < v) ∧ v < w → (∀ x ∈ t, x < w)
             └── forAll_gt_weaken -- symmetric
```

**Key insight**: Rotations only rearrange existing subtrees — they create no new
values. Every BST fact in the input tree transfers directly to the output, sometimes
requiring transitivity (`forAll_lt_weaken`/`forAll_gt_weaken`) when a subtree moves
under a different pivot.

**Reading `isBST_balance`**: After `simp only [IsBST, ForAll] at *`, all hypotheses
and the goal become nested conjunctions of `<` and `IsBST`/`ForAll` facts. The
projection paths (e.g. `hl.2.2.1.2.1`) navigate these right-associated `∧` chains:
- `.1` = left component of `∧`
- `.2` = right component of `∧`
- `.2.1` = left component of the right component
- etc.
-/

section NatProofs

/-- Bound weakening (upper): if every value in `t` is less than `v`, and `v < w`,
then every value in `t` is less than `w`.

We need this when a rotation moves a subtree from under pivot `v` to under a larger
pivot `w`. For example, in the left-left rotation, subtrees `a` and `b` were known
to have values `< x` and need to be shown to have values `< y` (where `x < y`). -/
theorem forAll_lt_weaken {v w : Nat} {t : Tree Nat} (hvw : v < w)
    (h : ForAll (· < v) t) : ForAll (· < w) t := by
  induction t with
  | leaf => trivial
  | node _ l x r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans h.2.1 hvw, ihr h.2.2⟩

/-- Bound weakening (lower): if every value in `t` is greater than `v`, and `w < v`,
then every value in `t` is greater than `w`. Symmetric to `forAll_lt_weaken`. -/
theorem forAll_gt_weaken {v w : Nat} {t : Tree Nat} (hwv : w < v)
    (h : ForAll (v < ·) t) : ForAll (w < ·) t := by
  induction t with
  | leaf => trivial
  | node _ l x r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans hwv h.2.1, ihr h.2.2⟩

/-- `ForAll p` distributes through `balance`: if `p` holds for all of `l`, for `v`,
and for all of `r`, then it holds for all of `balance color l v r`.

This is straightforward because `balance` only rearranges subtrees without creating
or discarding any values. -/
theorem forAll_balance {p : Nat → Prop} {c l v r} :
    ForAll p l → p v → ForAll p r → ForAll p (balance c l v r) := by
  intro hl hv hr
  unfold balance
  split <;> simp_all [ForAll]

/-- **The main workhorse**: `balance` preserves the BST invariant.

For each of the five arms of `balance` (four rotations + identity), we show that
`IsBST` holds for the output given `IsBST` inputs and appropriate ordering bounds.

**Proof technique**: After `simp only [IsBST, ForAll] at *`, hypotheses and the goal
are nested `∧`-chains. We split the goal into subgoals with `refine ⟨..., ?_, ...⟩`
and close each by extracting the matching fact from a hypothesis (via `.1`/`.2`
projections) or by applying `forAll_lt_weaken`/`forAll_gt_weaken` for transitivity.

For the left-left case (`l = node red (node red a x b) y c₁`):
- `hl.1.*` — BST facts about the inner node `(a, x, b)`
- `hl.2.1` — `IsBST c₁`
- `hl.2.2.1.*` — `ForAll (· < y)` over `(a, x, b)` (bounds through pivot `y`)
- `hl.2.2.2` — `ForAll (y < ·) c₁`
- `hltl.*` — `ForAll (· < z)` distributed over the whole left subtree
- `hltr` — `ForAll (z < ·)` over `d` (the right subtree, unchanged)
The other rotation cases follow the same pattern with different subtree positions. -/
theorem isBST_balance {c l v r} :
    IsBST l → IsBST r →
    ForAll (· < v) l → ForAll (v < ·) r →
    IsBST (balance c l v r) := by
  intro hl hr hltl hltr
  unfold balance
  split
  · -- Left-left rotation: R(R(a,x,b), y, c₁) z d  →  R(B(a,x,b), y, B(c₁,z,d))
    simp only [IsBST, ForAll] at *
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
      first
      | exact hl.1.1                                         -- IsBST a
      | exact hl.1.2.1                                       -- IsBST b
      | exact hl.1.2.2.1                                     -- ForAll (· < x) a
      | exact hl.1.2.2.2                                     -- ForAll (x < ·) b
      | exact hl.2.1                                         -- IsBST c₁
      | exact hr                                             -- IsBST d
      | exact hl.2.2.1.2.1                                   -- x < y
      | exact hl.2.2.2                                       -- ForAll (y < ·) c₁
      | exact (forAll_lt_weaken hl.2.2.1.2.1 hl.1.2.2.1)    -- ForAll (· < y) a  (was < x, weaken by x < y)
      | exact (forAll_lt_weaken hl.2.2.1.2.1 hl.1.2.2.2)    -- ForAll (· < y) b  (symmetric)
      | exact hltl.2.2                                       -- ForAll (· < z) c₁
      | exact (forAll_gt_weaken hltl.2.1 hltr)               -- ForAll (y < ·) d  (was z <, weaken by y < z)
      | exact hl.2.2.1.1                                     -- ForAll (· < y) a  (direct)
      | exact hl.2.2.1.2.2                                   -- ForAll (· < y) b  (direct)
      | exact hltl.2.1                                       -- y < z
      | exact hltr                                           -- ForAll (z < ·) d
  · -- Left-right rotation: R(a, x, R(b,y,c₁)) z d  →  R(B(a,x,b), y, B(c₁,z,d))
    simp only [IsBST, ForAll] at *
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
      first
      | exact hl.1
      | exact hl.2.2.1.2.1
      | exact hl.2.1.1
      | exact hl.2.1.2.1
      | exact hl.2.1.2.2.1
      | exact hl.2.1.2.2.2
      | exact hl.2.2.1
      | exact hl.2.2.2.1
      | exact (forAll_lt_weaken hl.2.2.2.2.1 hl.2.2.1)
      | exact (forAll_lt_weaken hl.2.2.2.2.1 hl.2.2.2.1)
      | exact hr
      | exact hltl.2.2.2.2
      | exact hltl.2.2.2.1
      | exact (forAll_gt_weaken hltl.2.2.2.1 hltr)
      | exact hl.2.2.2.2.1
      | exact hl.2.2.2.2.2
      | exact hltl.2.2.1
      | exact hltl.2.1
      | exact hltr
  · -- Right-left rotation: a x R(R(b,y,c₁), z, d)  →  R(B(a,x,b), y, B(c₁,z,d))
    simp only [IsBST, ForAll] at *
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
      first
      | exact hl
      | exact hr.1.1
      | exact hr.1.2.1
      | exact hr.1.2.2.1
      | exact hr.1.2.2.2
      | exact hr.2.1
      | exact hltl
      | exact (forAll_lt_weaken hltr.1.2.1 hltl)
      | exact (forAll_lt_weaken hltr.1.2.1 hr.1.2.2.1)
      | exact hltr.1.2.1
      | exact hr.2.2.1.2.1
      | exact hr.2.2.2
      | exact (forAll_gt_weaken hr.2.2.1.2.1 hr.2.2.2)
      | exact hr.2.2.1.1
      | exact hr.2.2.1.2.2
      | exact hltr.2.1
      | exact hltr.1.1
      | exact hltr.1.2.2
  · -- Right-right rotation: a x R(b, y, R(c₁,z,d))  →  R(B(a,x,b), y, B(c₁,z,d))
    simp only [IsBST, ForAll] at *
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
      first
      | exact hl
      | exact hr.1
      | exact hr.2.1.1
      | exact hr.2.1.2.1
      | exact hr.2.1.2.2.1
      | exact hr.2.1.2.2.2
      | exact hltl
      | exact (forAll_lt_weaken hltr.2.1 hltl)
      | exact (forAll_lt_weaken hltr.2.1 hr.2.2.1)
      | exact hltr.2.1
      | exact hr.2.2.2.1
      | exact hr.2.2.2.2.1
      | exact hr.2.2.2.2.2
      | exact (forAll_gt_weaken hr.2.2.2.2.1 hr.2.2.2.2.2)
      | exact hr.2.2.1
      | exact hr.2.2.2.2.1
      | exact hltr.1
      | exact hltr.2.2.1
      | exact hltr.2.2.2
  · -- No rotation: the node didn't match any violation pattern.
    exact ⟨hl, hr, hltl, hltr⟩

/-- Inserting a value that is `< v` into a tree where everything is `< v` preserves
the bound. This follows from `forAll_balance` (insertion rearranges but doesn't add
values that could violate the bound) and the fact that `x < v`. -/
theorem forAll_lt_ins {x v : Nat} {t : Tree Nat} (hxv : x < v)
    (h : ForAll (· < v) t) : ForAll (· < v) (ins x t) := by
  induction t with
  | leaf => simp [ins, ForAll]; exact hxv
  | node c l w r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hw, hr⟩ := h
    unfold ins; split
    · exact forAll_balance (ihl hl) hw hr     -- inserted left: recurse, then balance
    · simp [ForAll]; exact ⟨hl, hw, hr⟩       -- duplicate: tree unchanged
    · exact forAll_balance hl hw (ihr hr)      -- inserted right: recurse, then balance

/-- Symmetric to `forAll_lt_ins`: inserting `x > v` preserves a `> v` bound. -/
theorem forAll_gt_ins {x v : Nat} {t : Tree Nat} (hvx : v < x)
    (h : ForAll (v < ·) t) : ForAll (v < ·) (ins x t) := by
  induction t with
  | leaf => simp [ins, ForAll]; exact hvx
  | node c l w r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hw, hr⟩ := h
    unfold ins; split
    · exact forAll_balance (ihl hl) hw hr
    · simp [ForAll]; exact ⟨hl, hw, hr⟩
    · exact forAll_balance hl hw (ihr hr)

/-- `ins` preserves the BST invariant.

We induct on the tree and case-split on `compare x v`:
- `x < v`: we recurse into the left subtree. The result is a BST by `isBST_balance`,
  using `forAll_lt_ins` to show the new left subtree still has all values `< v`.
- `x = v`: the tree is unchanged (duplicate).
- `x > v`: symmetric to the `< v` case. -/
theorem isBST_ins {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (ins x t) := by
  induction t with
  | leaf => simp [ins, IsBST, ForAll]
  | node c l v r ihl ihr =>
    simp only [IsBST] at h
    obtain ⟨hl, hr, hltl, hltr⟩ := h
    unfold ins; split
    · -- x < v: insert into left subtree, then balance
      rename_i hlt; rw [Nat.compare_eq_lt] at hlt
      exact isBST_balance (ihl hl) hr (forAll_lt_ins hlt hltl) hltr
    · -- x = v: duplicate, tree unchanged
      exact ⟨hl, hr, hltl, hltr⟩
    · -- x > v: insert into right subtree, then balance
      rename_i hgt; rw [Nat.compare_eq_gt] at hgt
      exact isBST_balance hl (ihr hr) hltl (forAll_gt_ins hgt hltr)

/-- `makeBlack` preserves the BST invariant. Recoloring the root doesn't change
the tree's structure or values, so the ordering property is unaffected. -/
theorem isBST_makeBlack {t : Tree Nat} (h : IsBST t) : IsBST (makeBlack t) := by
  unfold makeBlack; split
  · simp only [IsBST] at h; exact h
  · trivial

/-- **Main theorem**: `insert` preserves the BST ordering invariant.

Proof: `insert x t = makeBlack (ins x t)`. By `isBST_ins`, the inner `ins` call
preserves `IsBST`. By `isBST_makeBlack`, recoloring the root also preserves it. -/
theorem isBST_insert {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (insert x t) :=
  isBST_makeBlack (isBST_ins h)

end NatProofs

end RBTree
