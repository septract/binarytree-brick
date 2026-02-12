import Rbtree.Classic
import Rbtree.DoubleBlack

/-!
# Equivalence Between Classic and DoubleBlack Red-Black Trees

This module defines an embedding from Classic (2-color) trees into DoubleBlack (4-color)
trees and proves structural equivalence theorems: the embedding preserves `toList`,
`contains`, and can be round-tripped via `project`.
-/

namespace RBTree.Equiv

/-- Embed a Classic color into a DoubleBlack color. -/
def embedColor : Classic.Color → DoubleBlack.Color
  | Classic.Color.red   => DoubleBlack.Color.red
  | Classic.Color.black => DoubleBlack.Color.black

/-- Embed a Classic tree into the DoubleBlack type system. -/
def embed : Classic.Tree α → DoubleBlack.Tree α
  | Classic.Tree.leaf => DoubleBlack.Tree.leaf
  | Classic.Tree.node c l v r =>
    DoubleBlack.Tree.node (embedColor c) (embed l) v (embed r)

/-- Project a DoubleBlack color back to Classic (fails on transient colors). -/
def projectColor : DoubleBlack.Color → Option Classic.Color
  | DoubleBlack.Color.red           => some Classic.Color.red
  | DoubleBlack.Color.black         => some Classic.Color.black
  | DoubleBlack.Color.doubleBlack   => none
  | DoubleBlack.Color.negativeBlack => none

/-- Project a DoubleBlack tree back to Classic (fails if transient nodes exist). -/
def project : DoubleBlack.Tree α → Option (Classic.Tree α)
  | DoubleBlack.Tree.leaf           => some Classic.Tree.leaf
  | DoubleBlack.Tree.doubleBlackLeaf => none
  | DoubleBlack.Tree.node c l v r  => do
    let c' ← projectColor c
    let l' ← project l
    let r' ← project r
    return Classic.Tree.node c' l' v r'

-- ════════════════════════════════════════════════════════════════════════════════
-- Structural equivalence theorems
-- ════════════════════════════════════════════════════════════════════════════════

theorem embed_preserves_toList (t : Classic.Tree α) :
    DoubleBlack.toList (embed t) = Classic.toList t := by
  induction t with
  | leaf => rfl
  | node c l v r ihl ihr =>
    simp only [embed, DoubleBlack.toList, Classic.toList, ihl, ihr]

theorem embed_preserves_contains [Ord α] (x : α) (t : Classic.Tree α) :
    DoubleBlack.contains x (embed t) = Classic.contains x t := by
  induction t with
  | leaf => rfl
  | node c l v r ihl ihr =>
    simp only [embed, DoubleBlack.contains, Classic.contains]
    cases compare x v <;> simp [ihl, ihr]

theorem embed_preserves_size (t : Classic.Tree α) :
    DoubleBlack.size (embed t) = Classic.size t := by
  induction t with
  | leaf => rfl
  | node c l v r ihl ihr =>
    simp only [embed, DoubleBlack.size, Classic.size, ihl, ihr]

theorem project_embed_id (t : Classic.Tree α) :
    project (embed t) = some t := by
  induction t with
  | leaf => rfl
  | node c l v r ihl ihr =>
    simp only [embed, project, bind, Option.bind]
    rw [ihl, ihr]
    cases c <;> simp [embedColor, projectColor]

-- ════════════════════════════════════════════════════════════════════════════════
-- Operational equivalence (stretch goals — require BST machinery)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Both `fromList` implementations produce the same sorted contents. -/
theorem fromList_equiv (xs : List Nat) :
    DoubleBlack.toList (DoubleBlack.fromList xs) =
    Classic.toList (Classic.fromList xs) := by
  sorry

end RBTree.Equiv
