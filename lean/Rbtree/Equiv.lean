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
-- Operational equivalence
-- ════════════════════════════════════════════════════════════════════════════════

/-! ### Key insight: balance preserves in-order traversal

Both `Classic.balance` and `DoubleBlack.balance` only rearrange subtrees — they never
create or discard values. So the in-order traversal (`toList`) is invariant under
balancing. We prove this for each balance function, then lift it through `ins`,
`makeBlack`, and `insert` to get `fromList_equiv`. -/

theorem classic_toList_balance (c : Classic.Color) (l : Classic.Tree α) (v : α)
    (r : Classic.Tree α) :
    Classic.toList (Classic.balance c l v r) = Classic.toList l ++ [v] ++ Classic.toList r := by
  unfold Classic.balance
  split <;> simp [Classic.toList, List.append_assoc]

theorem db_toList_balanceCore (c : DoubleBlack.Color) (l : DoubleBlack.Tree α) (v : α)
    (r : DoubleBlack.Tree α) :
    DoubleBlack.toList (DoubleBlack.balanceCore c l v r) =
    DoubleBlack.toList l ++ [v] ++ DoubleBlack.toList r := by
  unfold DoubleBlack.balanceCore
  split <;> simp [DoubleBlack.toList, List.append_assoc]

theorem db_toList_balance (c : DoubleBlack.Color) (l : DoubleBlack.Tree α) (v : α)
    (r : DoubleBlack.Tree α) :
    DoubleBlack.toList (DoubleBlack.balance c l v r) =
    DoubleBlack.toList l ++ [v] ++ DoubleBlack.toList r := by
  unfold DoubleBlack.balance
  split
  · -- NB left child case
    simp [DoubleBlack.toList, db_toList_balanceCore, List.append_assoc]
  · -- NB right child case
    simp [DoubleBlack.toList, db_toList_balanceCore, List.append_assoc]
  · -- Delegate to balanceCore
    exact db_toList_balanceCore c l v r

theorem classic_toList_makeBlack (t : Classic.Tree α) :
    Classic.toList (Classic.makeBlack t) = Classic.toList t := by
  cases t with
  | leaf => rfl
  | node c l v r => simp [Classic.makeBlack, Classic.toList]

theorem db_toList_makeBlack (t : DoubleBlack.Tree α) :
    DoubleBlack.toList (DoubleBlack.makeBlack t) = DoubleBlack.toList t := by
  cases t with
  | leaf => rfl
  | doubleBlackLeaf => rfl
  | node c l v r => simp [DoubleBlack.makeBlack, DoubleBlack.toList]

theorem toList_ins_eq [Ord α] (x : α) (t : Classic.Tree α) :
    DoubleBlack.toList (DoubleBlack.ins x (embed t)) =
    Classic.toList (Classic.ins x t) := by
  induction t with
  | leaf => simp [embed, Classic.ins, DoubleBlack.ins, Classic.toList, DoubleBlack.toList]
  | node c l v r ihl ihr =>
    simp only [embed, Classic.ins, DoubleBlack.ins]
    split
    · -- x < v
      rename_i heq; simp only [heq]
      rw [db_toList_balance, classic_toList_balance, ihl, embed_preserves_toList]
    · -- x = v
      rename_i heq; simp only [heq, DoubleBlack.toList, Classic.toList, embed_preserves_toList]
    · -- x > v
      rename_i heq; simp only [heq]
      rw [db_toList_balance, classic_toList_balance, ihr, embed_preserves_toList]

theorem toList_insert_eq [Ord α] (x : α) (t : Classic.Tree α) :
    DoubleBlack.toList (DoubleBlack.insert x (embed t)) =
    Classic.toList (Classic.insert x t) := by
  simp only [Classic.insert, DoubleBlack.insert]
  rw [db_toList_makeBlack, classic_toList_makeBlack, toList_ins_eq]

/-! ### Embedding commutes with operations

To prove `fromList_equiv`, we show that `embed` commutes with `balance`, `ins`,
`makeBlack`, `insert`, and `fromList`. Then the result follows from
`embed_preserves_toList`. -/

theorem embed_makeBlack (t : Classic.Tree α) :
    embed (Classic.makeBlack t) = DoubleBlack.makeBlack (embed t) := by
  cases t with
  | leaf => rfl
  | node c l v r => simp [Classic.makeBlack, DoubleBlack.makeBlack, embed, embedColor]

section EmbedBalance
attribute [local simp] Classic.balance embed embedColor DoubleBlack.balance DoubleBlack.balanceCore

theorem embed_balance (c : Classic.Color) (l : Classic.Tree α) (v : α)
    (r : Classic.Tree α) :
    embed (Classic.balance c l v r) =
    DoubleBlack.balance (embedColor c) (embed l) v (embed r) := by
  cases c
  · -- c = red: no rotation in either implementation
    simp
  · -- c = black: exhaustive case analysis on tree structure resolves both
    -- Classic.balance and DoubleBlack.balanceCore pattern matches simultaneously.
    cases l with
    | leaf =>
      cases r with
      | leaf => simp
      | node cr lr vr rr =>
        cases cr <;> (try simp)
        -- cr = red: need subtree colors to determine RL/RR patterns
        cases lr with
        | leaf =>
          cases rr with
          | leaf => simp
          | node crr _ _ _ => cases crr <;> simp
        | node clr _ _ _ =>
          cases clr <;> (try simp)
          cases rr with
          | leaf => simp
          | node crr _ _ _ => cases crr <;> simp
    | node cl ll vl rl =>
      cases cl with
      | black =>
        cases r with
        | leaf => simp
        | node cr lr vr rr =>
          cases cr <;> (try simp)
          cases lr with
          | leaf =>
            cases rr with
            | leaf => simp
            | node crr _ _ _ => cases crr <;> simp
          | node clr _ _ _ =>
            cases clr <;> (try simp)
            cases rr with
            | leaf => simp
            | node crr _ _ _ => cases crr <;> simp
      | red =>
        -- Left subtree is red; check children for LL/LR patterns
        cases ll with
        | leaf =>
          cases rl with
          | leaf =>
            cases r with
            | leaf => simp
            | node cr lr vr rr =>
              cases cr <;> (try simp)
              cases lr with
              | leaf =>
                cases rr with
                | leaf => simp
                | node crr _ _ _ => cases crr <;> simp
              | node clr _ _ _ =>
                cases clr <;> (try simp)
                cases rr with
                | leaf => simp
                | node crr _ _ _ => cases crr <;> simp
          | node crl _ _ _ =>
            cases crl
            · simp
            · -- crl = black: no LL (ll=leaf), no LR (rl=black). Case-split r for RL/RR.
              cases r with
              | leaf => simp
              | node cr lr vr rr =>
                cases cr <;> (try simp)
                cases lr with
                | leaf =>
                  cases rr with
                  | leaf => simp
                  | node crr _ _ _ => cases crr <;> simp
                | node clr _ _ _ =>
                  cases clr <;> (try simp)
                  cases rr with
                  | leaf => simp
                  | node crr _ _ _ => cases crr <;> simp
        | node cll _ _ _ =>
          cases cll <;> (try simp)
          -- cll = black: no LL. Check rl for LR, then r for RL/RR
          cases rl with
          | leaf =>
            cases r with
            | leaf => simp
            | node cr lr vr rr =>
              cases cr <;> (try simp)
              cases lr with
              | leaf =>
                cases rr with
                | leaf => simp
                | node crr _ _ _ => cases crr <;> simp
              | node clr _ _ _ =>
                cases clr <;> (try simp)
                cases rr with
                | leaf => simp
                | node crr _ _ _ => cases crr <;> simp
          | node crl _ _ _ =>
            cases crl
            · simp
            · -- crl = black: no LL (ll=black), no LR (rl=black). Case-split r for RL/RR.
              cases r with
              | leaf => simp
              | node cr lr vr rr =>
                cases cr <;> (try simp)
                cases lr with
                | leaf =>
                  cases rr with
                  | leaf => simp
                  | node crr _ _ _ => cases crr <;> simp
                | node clr _ _ _ =>
                  cases clr <;> (try simp)
                  cases rr with
                  | leaf => simp
                  | node crr _ _ _ => cases crr <;> simp

end EmbedBalance

theorem embed_ins [Ord α] (x : α) (t : Classic.Tree α) :
    embed (Classic.ins x t) = DoubleBlack.ins x (embed t) := by
  induction t with
  | leaf => simp [Classic.ins, DoubleBlack.ins, embed, embedColor]
  | node c l v r ihl ihr =>
    simp only [Classic.ins, DoubleBlack.ins, embed]
    split
    · rename_i heq; simp only [heq]; rw [embed_balance]; congr 1
    · rename_i heq; simp only [heq]; rfl
    · rename_i heq; simp only [heq]; rw [embed_balance]; congr 1

theorem embed_insert [Ord α] (x : α) (t : Classic.Tree α) :
    embed (Classic.insert x t) = DoubleBlack.insert x (embed t) := by
  simp only [Classic.insert, DoubleBlack.insert, embed_makeBlack, embed_ins]

theorem embed_fromList [Ord α] (xs : List α) :
    embed (Classic.fromList xs) = DoubleBlack.fromList xs := by
  simp only [Classic.fromList, DoubleBlack.fromList]
  suffices h : ∀ t, embed (xs.foldl (fun t x => Classic.insert x t) t) =
    xs.foldl (fun t x => DoubleBlack.insert x t) (embed t) from h Classic.Tree.leaf
  induction xs with
  | nil => intro t; rfl
  | cons x xs ih =>
    intro t; simp only [List.foldl]; rw [← embed_insert]; exact ih _

/-- Both `fromList` implementations produce the same sorted contents. -/
theorem fromList_equiv (xs : List Nat) :
    DoubleBlack.toList (DoubleBlack.fromList xs) =
    Classic.toList (Classic.fromList xs) := by
  rw [← embed_fromList, embed_preserves_toList]

end RBTree.Equiv
