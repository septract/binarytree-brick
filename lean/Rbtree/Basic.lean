/-
  Red-Black Tree implementation in Lean 4.

  A red-black tree is a self-balancing binary search tree where each node
  carries a color (Red or Black) and the following invariants hold:

  1. Every node is either red or black.
  2. The root is black.
  3. No red node has a red child.
  4. Every path from root to a leaf has the same number of black nodes.

  This module implements:
  - The core data type (`RBTree`)
  - Membership test (`contains`)
  - Insertion with Okasaki-style balancing (`insert`)
  - Conversion to sorted list (`toList`)
  - A proof that the BST ordering invariant is preserved by `insert`
-/

namespace RBTree

/-- Node color: Red or Black. -/
inductive Color where
  | red
  | black
  deriving Repr, BEq, DecidableEq

/-- A red-black tree storing values of type `α`. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Color → Tree α → α → Tree α → Tree α
  deriving Repr

open Color Tree

variable {α : Type} [Ord α] [BEq α]

-- ══════════════════════════════════════════════════════════════════════
-- Core operations
-- ══════════════════════════════════════════════════════════════════════

/-- Test whether a value is in the tree. -/
def contains (x : α) : Tree α → Bool
  | leaf => false
  | node _ l v r =>
    match compare x v with
    | .lt => contains x l
    | .eq => true
    | .gt => contains x r

/-- Okasaki's balance function: fix red-red violations after insertion. -/
def balance (c : Color) (l : Tree α) (v : α) (r : Tree α) : Tree α :=
  match c, l, v, r with
  -- Left-left case
  | black, node red (node red a x b) y c, z, d =>
    node red (node black a x b) y (node black c z d)
  -- Left-right case
  | black, node red a x (node red b y c), z, d =>
    node red (node black a x b) y (node black c z d)
  -- Right-left case
  | black, a, x, node red (node red b y c) z d =>
    node red (node black a x b) y (node black c z d)
  -- Right-right case
  | black, a, x, node red b y (node red c z d) =>
    node red (node black a x b) y (node black c z d)
  -- No violation
  | c, l, v, r => node c l v r

/-- Insert into the tree (internal: may produce a red root). -/
def ins (x : α) : Tree α → Tree α
  | leaf => node red leaf x leaf
  | node c l v r =>
    match compare x v with
    | .lt => balance c (ins x l) v r
    | .eq => node c l v r
    | .gt => balance c l v (ins x r)

/-- Force the root to black. -/
def makeBlack : Tree α → Tree α
  | node _ l v r => node black l v r
  | leaf => leaf

/-- Insert a value into the red-black tree. -/
def insert (x : α) (t : Tree α) : Tree α :=
  makeBlack (ins x t)

/-- In-order traversal producing a sorted list. -/
def toList : Tree α → List α
  | leaf => []
  | node _ l v r => toList l ++ [v] ++ toList r

/-- Build a tree from a list of values. -/
def fromList (xs : List α) : Tree α :=
  xs.foldl (fun t x => insert x t) leaf

/-- Number of elements in the tree. -/
def size : Tree α → Nat
  | leaf => 0
  | node _ l _ r => 1 + size l + size r

/-- Height of the tree. -/
def height : Tree α → Nat
  | leaf => 0
  | node _ l _ r => 1 + max (height l) (height r)

/-- Count the black height (along the leftmost path). -/
def blackHeight : Tree α → Nat
  | leaf => 1
  | node c l _ _ =>
    (match c with | black => 1 | red => 0) + blackHeight l

-- ══════════════════════════════════════════════════════════════════════
-- BST invariant and proof that insert preserves it
-- ══════════════════════════════════════════════════════════════════════

/-- Every element in the tree satisfies predicate `p`. -/
def ForAll (p : α → Prop) : Tree α → Prop
  | leaf => True
  | node _ l v r => ForAll p l ∧ p v ∧ ForAll p r

/-- The BST ordering invariant. -/
def IsBST : Tree Nat → Prop
  | leaf => True
  | node _ l v r =>
    IsBST l ∧ IsBST r ∧ ForAll (· < v) l ∧ ForAll (v < ·) r

section NatProofs

/-- Monotonicity: weaken an upper bound in `ForAll`. -/
theorem forAll_lt_weaken {v w : Nat} {t : Tree Nat} (hvw : v < w)
    (h : ForAll (· < v) t) : ForAll (· < w) t := by
  induction t with
  | leaf => trivial
  | node _ l x r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans h.2.1 hvw, ihr h.2.2⟩

/-- Monotonicity: weaken a lower bound in `ForAll`. -/
theorem forAll_gt_weaken {v w : Nat} {t : Tree Nat} (hwv : w < v)
    (h : ForAll (v < ·) t) : ForAll (w < ·) t := by
  induction t with
  | leaf => trivial
  | node _ l x r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans hwv h.2.1, ihr h.2.2⟩

/-- `ForAll` distributes over `balance`. -/
theorem forAll_balance {p : Nat → Prop} {c l v r} :
    ForAll p l → p v → ForAll p r → ForAll p (balance c l v r) := by
  intro hl hv hr
  unfold balance
  split <;> simp_all [ForAll]

/-- `IsBST` is preserved by `balance`. -/
theorem isBST_balance {c l v r} :
    IsBST l → IsBST r →
    ForAll (· < v) l → ForAll (v < ·) r →
    IsBST (balance c l v r) := by
  intro hl hr hltl hltr
  unfold balance
  -- Handle each rotation case and the identity case.
  -- After split + simp_all, remaining goals need ForAll monotonicity.
  split
  · -- Left-left: l = node red (node red a x b) y cc, r = d
    simp only [IsBST, ForAll] at *
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
      first
      | exact hl.1.1
      | exact hl.1.2.1
      | exact hl.1.2.2.1
      | exact hl.1.2.2.2
      | exact hl.2.1
      | exact hr
      | exact hl.2.2.1.2.1
      | exact hl.2.2.2
      | exact (forAll_lt_weaken hl.2.2.1.2.1 hl.1.2.2.1)
      | exact (forAll_lt_weaken hl.2.2.1.2.1 hl.1.2.2.2)
      | exact hltl.2.2
      | exact (forAll_gt_weaken hltl.2.1 hltr)
      | exact hl.2.2.1.1
      | exact hl.2.2.1.2.2
      | exact hltl.2.1
      | exact hltr
  · -- Left-right: l = node red a x (node red b y cc)
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
  · -- Right-left: r = node red (node red b y cc) z d
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
  · -- Right-right: r = node red b y (node red cc z d)
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
  · -- Identity: no rotation needed
    exact ⟨hl, hr, hltl, hltr⟩

/-- `ForAll (· < v)` is preserved by `ins x` when `x < v`. -/
theorem forAll_lt_ins {x v : Nat} {t : Tree Nat} (hxv : x < v)
    (h : ForAll (· < v) t) : ForAll (· < v) (ins x t) := by
  induction t with
  | leaf => simp [ins, ForAll]; exact hxv
  | node c l w r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hw, hr⟩ := h
    unfold ins; split
    · exact forAll_balance (ihl hl) hw hr
    · simp [ForAll]; exact ⟨hl, hw, hr⟩
    · exact forAll_balance hl hw (ihr hr)

/-- `ForAll (v < ·)` is preserved by `ins x` when `v < x`. -/
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

/-- `ins` preserves the BST invariant. -/
theorem isBST_ins {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (ins x t) := by
  induction t with
  | leaf => simp [ins, IsBST, ForAll]
  | node c l v r ihl ihr =>
    simp only [IsBST] at h
    obtain ⟨hl, hr, hltl, hltr⟩ := h
    unfold ins; split
    · rename_i hlt; rw [Nat.compare_eq_lt] at hlt
      exact isBST_balance (ihl hl) hr (forAll_lt_ins hlt hltl) hltr
    · exact ⟨hl, hr, hltl, hltr⟩
    · rename_i hgt; rw [Nat.compare_eq_gt] at hgt
      exact isBST_balance hl (ihr hr) hltl (forAll_gt_ins hgt hltr)

/-- `IsBST` is preserved by `makeBlack`. -/
theorem isBST_makeBlack {t : Tree Nat} (h : IsBST t) : IsBST (makeBlack t) := by
  unfold makeBlack; split
  · simp only [IsBST] at h; exact h
  · trivial

/-- **Main theorem**: `insert` preserves the BST ordering invariant. -/
theorem isBST_insert {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (insert x t) :=
  isBST_makeBlack (isBST_ins h)

end NatProofs

end RBTree
