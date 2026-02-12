/-
  Shared definitions for Red-Black Tree implementations.

  This module provides abstract interfaces that both the Classic (2-color)
  and DoubleBlack (4-color) implementations can satisfy.
-/

namespace RBTree

/-- Abstract interface for red-black tree implementations. -/
class Impl (T : Type → Type) where
  empty    {α : Type} : T α
  insert   {α : Type} [Ord α] [BEq α] : α → T α → T α
  contains {α : Type} [Ord α] [BEq α] : α → T α → Bool
  toList   {α : Type} : T α → List α
  size     {α : Type} : T α → Nat

/-- Extended interface for implementations that also support deletion. -/
class ImplWithDelete (T : Type → Type) extends Impl T where
  delete {α : Type} [Ord α] [BEq α] : α → T α → T α

end RBTree
