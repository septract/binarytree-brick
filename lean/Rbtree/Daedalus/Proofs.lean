import Rbtree.Daedalus
import Rbtree.Classic

/-!
# Proofs for the Daedalus Red-Black Tree

## Part A: Split-rebalance equivalence

The Daedalus C++ code splits Okasaki's unified `balance` into `setRebalanceLeft`
(LL + LR cases) and `setRebalanceRight` (RL + RR cases). We prove these are
equivalent to `balance` when the *other* subtree has no red-red violation —
which is always the case during insertion, since `ins` only modifies one subtree.

## Part B: BST invariant preservation

Following the same proof architecture as `Classic/Proofs.lean`, we prove that
`insert` preserves the BST ordering invariant on keys. We prove the BST lemmas
directly for `setRebalanceLeft`/`setRebalanceRight` (3 cases each) rather than
going through the unified `balance` (5 cases).

## Part C: Cross-implementation equivalence with Classic

We define a `toKeys` embedding that strips values from a Daedalus map tree,
producing a Classic set tree. We prove this embedding commutes with `balance`
(unconditionally) and with `insert` (for trees with no red-red violations),
establishing that Daedalus and Classic produce identical key structures.
-/

namespace RBTree.Daedalus

open Color Tree

-- ════════════════════════════════════════════════════════════════════════════════
-- Part A: Split-rebalance = balance equivalence
-- ════════════════════════════════════════════════════════════════════════════════

/-! ### When does the split matter?

`balance c l k v r` inspects *both* `l` and `r` for red-red violations.
`setRebalanceLeft c l k v r` only inspects `l` (ignoring `r`).

They differ only when `r` has a top-level red-red violation (RL or RR pattern),
which would cause `balance` to fire the RL/RR case instead of the default.
During insertion, the unmodified subtree comes from a valid red-black tree and
thus has no red-red violation, so the split is always correct. -/

/-- A tree has no red-red violation at its top level: a red root does not have
a red child. This is trivially true for black-rooted trees and empty trees. -/
def NoRedRedChildren : Tree α β → Prop
  | node red (node red _ _ _ _) _ _ _ => False
  | node red _ _ _ (node red _ _ _ _) => False
  | _ => True

/-! ### r-block pattern

The default case of `setRebalanceLeft` (no LL/LR rotation) produces
`node c newLeft k v r`. To show `balance` also defaults, we must rule out
balance's RL/RR arms by case-splitting on `r` until all discriminants are
concrete constructors, using `NoRedRedChildren r` to eliminate impossible cases.

The same pattern (symmetric on `l`) appears in `setRebalanceRight_eq_balance`.
Each "r-block" or "l-block" below is a ~10-line case analysis establishing that
`balance` takes its default arm when the opposite subtree has no red-red. -/

/-- `setRebalanceLeft` equals `balance` when the right subtree has no red-red violation.

This is the core soundness theorem for the Daedalus split-rebalance design.
When `r` satisfies `NoRedRedChildren`, the RL and RR cases of `balance` cannot
fire, so `balance` only inspects the left subtree — exactly what
`setRebalanceLeft` does.

The proof exhaustively case-splits on `c`, `newLeft` (to determine which arm of
`setRebalanceLeft` fires), and `r` (to rule out `balance`'s RL/RR arms in the
default cases). The LL and LR rotation cases close by `rfl` since both functions
produce identical rotations. Default cases close by `rfl` once `r` is concrete
enough that `balance`'s match fully reduces. -/
theorem setRebalanceLeft_eq_balance {α β : Type} {c : Color} {newLeft : Tree α β}
    {k : α} {v : β} {r : Tree α β} (hr : NoRedRedChildren r) :
    setRebalanceLeft c newLeft k v r = balance c newLeft k v r := by
  cases c with
  | red => rfl
  | black =>
    cases newLeft with
    | empty =>
      -- No LL/LR (newLeft=empty). Case-split r for balance's RL/RR.
      cases r with
      | empty => rfl
      | node cr lr _ _ rr => cases cr with
        | black => rfl
        | red => cases lr with
          | empty => cases rr with
            | empty => rfl
            | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
          | node clr _ _ _ _ => cases clr with
            | red => exact hr.elim
            | black => cases rr with
              | empty => rfl
              | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
    | node cnl ll _ _ rl =>
      cases cnl with
      | black =>
        -- newLeft is black-rooted: no LL/LR. Case-split r.
        cases r with
        | empty => rfl
        | node cr lr _ _ rr => cases cr with
          | black => rfl
          | red => cases lr with
            | empty => cases rr with
              | empty => rfl
              | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
            | node clr _ _ _ _ => cases clr with
              | red => exact hr.elim
              | black => cases rr with
                | empty => rfl
                | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
      | red =>
        -- newLeft is red. Check children for LL/LR pattern.
        cases ll with
        | empty =>
          cases rl with
          | empty =>
            -- newLeft = R(empty, _, _, empty). No LL, no LR. Case-split r.
            cases r with
            | empty => rfl
            | node cr lr _ _ rr => cases cr with
              | black => rfl
              | red => cases lr with
                | empty => cases rr with
                  | empty => rfl
                  | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
                | node clr _ _ _ _ => cases clr with
                  | red => exact hr.elim
                  | black => cases rr with
                    | empty => rfl
                    | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
          | node crl _ _ _ _ =>
            cases crl with
            | black =>
              -- newLeft = R(empty, _, _, B(...)). No LL, no LR. Case-split r.
              cases r with
              | empty => rfl
              | node cr lr _ _ rr => cases cr with
                | black => rfl
                | red => cases lr with
                  | empty => cases rr with
                    | empty => rfl
                    | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
                  | node clr _ _ _ _ => cases clr with
                    | red => exact hr.elim
                    | black => cases rr with
                      | empty => rfl
                      | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
            | red => rfl  -- LR rotation: both functions produce identical result
        | node cll _ _ _ _ =>
          cases cll with
          | red => rfl  -- LL rotation: both functions produce identical result
          | black =>
            -- ll is black. No LL. Check rl for LR.
            cases rl with
            | empty =>
              -- No LR (rl=empty). Case-split r.
              cases r with
              | empty => rfl
              | node cr lr _ _ rr => cases cr with
                | black => rfl
                | red => cases lr with
                  | empty => cases rr with
                    | empty => rfl
                    | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
                  | node clr _ _ _ _ => cases clr with
                    | red => exact hr.elim
                    | black => cases rr with
                      | empty => rfl
                      | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
            | node crl _ _ _ _ =>
              cases crl with
              | black =>
                -- rl is black. No LR. Case-split r.
                cases r with
                | empty => rfl
                | node cr lr _ _ rr => cases cr with
                  | black => rfl
                  | red => cases lr with
                    | empty => cases rr with
                      | empty => rfl
                      | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
                    | node clr _ _ _ _ => cases clr with
                      | red => exact hr.elim
                      | black => cases rr with
                        | empty => rfl
                        | node crr _ _ _ _ => cases crr with | black => rfl | red => exact hr.elim
              | red => rfl  -- LR rotation

/-- Symmetric to `setRebalanceLeft_eq_balance`: `setRebalanceRight` equals
`balance` when the left subtree has no red-red violation.

The proof structure mirrors `setRebalanceLeft_eq_balance` with left and right
swapped: we case-split on `c`, `newRight` (for RL/RR), and `l` (for LL/LR with
`NoRedRedChildren l` eliminating impossible cases). -/
theorem setRebalanceRight_eq_balance {α β : Type} {c : Color} {l : Tree α β}
    {k : α} {v : β} {newRight : Tree α β} (hl : NoRedRedChildren l) :
    setRebalanceRight c l k v newRight = balance c l k v newRight := by
  cases c with
  | red => rfl
  | black =>
    cases newRight with
    | empty =>
      -- No RL/RR. Case-split l for balance's LL/LR.
      cases l with
      | empty => rfl
      | node cl ll _ _ lr => cases cl with
        | black => rfl
        | red => cases ll with
          | empty => cases lr with
            | empty => rfl
            | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
          | node cll _ _ _ _ => cases cll with
            | red => exact hl.elim
            | black => cases lr with
              | empty => rfl
              | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
    | node cnr lr _ _ rr =>
      cases cnr with
      | black =>
        -- newRight is black-rooted: no RL/RR. Case-split l.
        cases l with
        | empty => rfl
        | node cl ll _ _ lr => cases cl with
          | black => rfl
          | red => cases ll with
            | empty => cases lr with
              | empty => rfl
              | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
            | node cll _ _ _ _ => cases cll with
              | red => exact hl.elim
              | black => cases lr with
                | empty => rfl
                | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
      | red =>
        -- newRight is red. Check children for RL/RR pattern.
        cases lr with
        | empty =>
          cases rr with
          | empty =>
            -- newRight = R(empty, _, _, empty). No RL, no RR. Case-split l.
            cases l with
            | empty => rfl
            | node cl ll _ _ lr => cases cl with
              | black => rfl
              | red => cases ll with
                | empty => cases lr with
                  | empty => rfl
                  | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
                | node cll _ _ _ _ => cases cll with
                  | red => exact hl.elim
                  | black => cases lr with
                    | empty => rfl
                    | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
          | node crr _ _ _ _ =>
            cases crr with
            | black =>
              -- newRight = R(empty, _, _, B(...)). No RL, no RR. Case-split l.
              cases l with
              | empty => rfl
              | node cl ll _ _ lr => cases cl with
                | black => rfl
                | red => cases ll with
                  | empty => cases lr with
                    | empty => rfl
                    | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
                  | node cll _ _ _ _ => cases cll with
                    | red => exact hl.elim
                    | black => cases lr with
                      | empty => rfl
                      | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
            | red =>
              -- RR rotation: both produce same result, but need l concrete for balance.
              cases l with
              | empty => rfl
              | node cl ll _ _ lr => cases cl with
                | black => rfl
                | red => cases ll with
                  | empty => cases lr with
                    | empty => rfl
                    | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
                  | node cll _ _ _ _ => cases cll with
                    | red => exact hl.elim
                    | black => cases lr with
                      | empty => rfl
                      | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
        | node clr _ _ _ _ =>
          cases clr with
          | red =>
            -- RL rotation: both produce same result, but need l concrete for balance.
            cases l with
            | empty => rfl
            | node cl ll _ _ lr => cases cl with
              | black => rfl
              | red => cases ll with
                | empty => cases lr with
                  | empty => rfl
                  | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
                | node cll _ _ _ _ => cases cll with
                  | red => exact hl.elim
                  | black => cases lr with
                    | empty => rfl
                    | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
          | black =>
            -- lr is black. No RL. Check rr for RR.
            cases rr with
            | empty =>
              -- No RR (rr=empty). Case-split l.
              cases l with
              | empty => rfl
              | node cl ll _ _ lr => cases cl with
                | black => rfl
                | red => cases ll with
                  | empty => cases lr with
                    | empty => rfl
                    | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
                  | node cll _ _ _ _ => cases cll with
                    | red => exact hl.elim
                    | black => cases lr with
                      | empty => rfl
                      | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
            | node crr _ _ _ _ =>
              cases crr with
              | black =>
                -- rr is black. No RR. Case-split l.
                cases l with
                | empty => rfl
                | node cl ll _ _ lr => cases cl with
                  | black => rfl
                  | red => cases ll with
                    | empty => cases lr with
                      | empty => rfl
                      | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
                    | node cll _ _ _ _ => cases cll with
                      | red => exact hl.elim
                      | black => cases lr with
                        | empty => rfl
                        | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
              | red =>
                -- RR rotation: both produce same result, but need l concrete for balance.
                cases l with
                | empty => rfl
                | node cl ll _ _ lr => cases cl with
                  | black => rfl
                  | red => cases ll with
                    | empty => cases lr with
                      | empty => rfl
                      | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim
                    | node cll _ _ _ _ => cases cll with
                      | red => exact hl.elim
                      | black => cases lr with
                        | empty => rfl
                        | node clr _ _ _ _ => cases clr with | black => rfl | red => exact hl.elim

-- ════════════════════════════════════════════════════════════════════════════════
-- Part B: BST invariant preservation
-- ════════════════════════════════════════════════════════════════════════════════

section NatProofs

variable {β : Type}

/-- Every key stored in the tree satisfies predicate `p`. -/
def ForAll (p : α → Prop) : Tree α β → Prop
  | empty => True
  | node _ l k _ r => ForAll p l ∧ p k ∧ ForAll p r

/-- The BST ordering invariant on keys: for every `node _ l k _ r`,
all keys in `l` are less than `k`, and all keys in `r` are greater than `k`. -/
def IsBST : Tree Nat β → Prop
  | empty => True
  | node _ l k _ r =>
    IsBST l ∧ IsBST r ∧ ForAll (· < k) l ∧ ForAll (k < ·) r

theorem forAll_lt_weaken {v w : Nat} {t : Tree Nat β} (hvw : v < w)
    (h : ForAll (· < v) t) : ForAll (· < w) t := by
  induction t with
  | empty => trivial
  | node _ l x _ r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans h.2.1 hvw, ihr h.2.2⟩

theorem forAll_gt_weaken {v w : Nat} {t : Tree Nat β} (hwv : w < v)
    (h : ForAll (v < ·) t) : ForAll (w < ·) t := by
  induction t with
  | empty => trivial
  | node _ l x _ r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans hwv h.2.1, ihr h.2.2⟩

/-- `ForAll p` distributes through `setRebalanceLeft`. -/
theorem forAll_setRebalanceLeft {p : Nat → Prop} {c : Color} {newLeft : Tree Nat β}
    {k : Nat} {v : β} {r : Tree Nat β} :
    ForAll p newLeft → p k → ForAll p r →
    ForAll p (setRebalanceLeft c newLeft k v r) := by
  intro hl hk hr
  unfold setRebalanceLeft
  split <;> simp_all [ForAll]

/-- `ForAll p` distributes through `setRebalanceRight`. -/
theorem forAll_setRebalanceRight {p : Nat → Prop} {c : Color} {l : Tree Nat β}
    {k : Nat} {v : β} {newRight : Tree Nat β} :
    ForAll p l → p k → ForAll p newRight →
    ForAll p (setRebalanceRight c l k v newRight) := by
  intro hl hk hr
  unfold setRebalanceRight
  split <;> simp_all [ForAll]

/-- `setRebalanceLeft` preserves BST. Proved directly by case-splitting on the
three arms (LL rotation, LR rotation, no rotation).

The projection paths (e.g. `hl.2.2.1.2.1`) navigate right-associated `∧` chains
produced by `simp only [IsBST, ForAll]`:
- `.1` = left conjunct, `.2` = right conjunct
- `.2.1` = left of right, `.2.2.1` = left of right of right, etc. -/
theorem isBST_setRebalanceLeft {c : Color} {newLeft : Tree Nat β}
    {k : Nat} {v : β} {r : Tree Nat β} :
    IsBST newLeft → IsBST r →
    ForAll (· < k) newLeft → ForAll (k < ·) r →
    IsBST (setRebalanceLeft c newLeft k v r) := by
  intro hl hr hltl hltr
  unfold setRebalanceLeft
  split
  · -- LL rotation: newLeft = R(R(a,kx,b), ky, c₁)
    simp only [IsBST, ForAll] at *
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
      first
      | exact hl.1.1                                         -- IsBST a
      | exact hl.1.2.1                                       -- IsBST b
      | exact hl.1.2.2.1                                     -- ForAll (· < kx) a
      | exact hl.1.2.2.2                                     -- ForAll (kx < ·) b
      | exact hl.2.1                                         -- IsBST c₁
      | exact hr                                             -- IsBST r
      | exact hl.2.2.1.2.1                                   -- kx < ky
      | exact hl.2.2.2                                       -- ForAll (ky < ·) c₁
      | exact (forAll_lt_weaken hl.2.2.1.2.1 hl.1.2.2.1)    -- ForAll (· < ky) a
      | exact (forAll_lt_weaken hl.2.2.1.2.1 hl.1.2.2.2)    -- ForAll (· < ky) b
      | exact hltl.2.2                                       -- ForAll (· < k) c₁
      | exact (forAll_gt_weaken hltl.2.1 hltr)               -- ForAll (ky < ·) r
      | exact hl.2.2.1.1                                     -- ForAll (· < ky) a (direct)
      | exact hl.2.2.1.2.2                                   -- ForAll (· < ky) b (direct)
      | exact hltl.2.1                                       -- ky < k
      | exact hltr                                           -- ForAll (k < ·) r
  · -- LR rotation: newLeft = R(a, kx, R(b,ky,c₁))
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
  · -- No rotation: the node didn't match any violation pattern.
    exact ⟨hl, hr, hltl, hltr⟩

/-- `setRebalanceRight` preserves BST. Symmetric to `isBST_setRebalanceLeft`. -/
theorem isBST_setRebalanceRight {c : Color} {l : Tree Nat β}
    {k : Nat} {v : β} {newRight : Tree Nat β} :
    IsBST l → IsBST newRight →
    ForAll (· < k) l → ForAll (k < ·) newRight →
    IsBST (setRebalanceRight c l k v newRight) := by
  intro hl hr hltl hltr
  unfold setRebalanceRight
  split
  · -- RL rotation: newRight = R(R(b,ky,c₁), kz, d)
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
  · -- RR rotation: newRight = R(b, ky, R(c₁,kz,d))
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
  · -- No rotation
    exact ⟨hl, hr, hltl, hltr⟩

/-- Inserting a key less than `v` preserves the `ForAll (· < v)` bound. -/
theorem forAll_lt_ins {x : Nat} {xv : β} {v : Nat} {t : Tree Nat β} (hxv : x < v)
    (h : ForAll (· < v) t) : ForAll (· < v) (ins x xv t) := by
  induction t with
  | empty => simp [ins, ForAll]; exact hxv
  | node c l w wv r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hw, hr⟩ := h
    unfold ins; split
    · exact forAll_setRebalanceLeft (ihl hl) hw hr
    · simp [ForAll]; exact ⟨hl, hw, hr⟩
    · exact forAll_setRebalanceRight hl hw (ihr hr)

/-- Symmetric: inserting a key greater than `v` preserves the `ForAll (v < ·)` bound. -/
theorem forAll_gt_ins {x : Nat} {xv : β} {v : Nat} {t : Tree Nat β} (hvx : v < x)
    (h : ForAll (v < ·) t) : ForAll (v < ·) (ins x xv t) := by
  induction t with
  | empty => simp [ins, ForAll]; exact hvx
  | node c l w wv r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hw, hr⟩ := h
    unfold ins; split
    · exact forAll_setRebalanceLeft (ihl hl) hw hr
    · simp [ForAll]; exact ⟨hl, hw, hr⟩
    · exact forAll_setRebalanceRight hl hw (ihr hr)

/-- `ins` preserves the BST invariant. -/
theorem isBST_ins {x : Nat} {xv : β} {t : Tree Nat β} (h : IsBST t) :
    IsBST (ins x xv t) := by
  induction t with
  | empty => simp [ins, IsBST, ForAll]
  | node c l k kv r ihl ihr =>
    simp only [IsBST] at h
    obtain ⟨hl, hr, hltl, hltr⟩ := h
    unfold ins; split
    · rename_i hlt; rw [Nat.compare_eq_lt] at hlt
      exact isBST_setRebalanceLeft (ihl hl) hr (forAll_lt_ins hlt hltl) hltr
    · exact ⟨hl, hr, hltl, hltr⟩
    · rename_i hgt; rw [Nat.compare_eq_gt] at hgt
      exact isBST_setRebalanceRight hl (ihr hr) hltl (forAll_gt_ins hgt hltr)

/-- `makeBlack` preserves BST. -/
theorem isBST_makeBlack {t : Tree Nat β} (h : IsBST t) : IsBST (makeBlack t) := by
  unfold makeBlack; split
  · simp only [IsBST] at h; exact h
  · trivial

/-- **Main theorem**: `insert` preserves the BST ordering invariant. -/
theorem isBST_insert {x : Nat} {xv : β} {t : Tree Nat β} (h : IsBST t) :
    IsBST (insert x xv t) :=
  isBST_makeBlack (isBST_ins h)

end NatProofs

-- ════════════════════════════════════════════════════════════════════════════════
-- Part C: Cross-implementation equivalence with Classic
-- ════════════════════════════════════════════════════════════════════════════════

/-! ### Key-projection embedding

We define `embedColor` and `toKeys` to map Daedalus map trees to Classic set trees
by stripping values. Then we prove this embedding commutes with all operations,
establishing that the Daedalus implementation produces identical key structures
to the Classic implementation. -/

/-- Map Daedalus color to Classic color. Both have the same constructors. -/
def embedColor : Color → Classic.Color
  | red => Classic.Color.red
  | black => Classic.Color.black

/-- Strip values from a Daedalus map tree, producing a Classic set tree.
This is the key embedding for the equivalence proof. -/
def toKeys : Tree α β → Classic.Tree α
  | empty => Classic.Tree.leaf
  | node c l k _ r => Classic.Tree.node (embedColor c) (toKeys l) k (toKeys r)

/-- `toKeys` commutes with `makeBlack`. -/
theorem toKeys_makeBlack {α β : Type} {t : Tree α β} :
    toKeys (makeBlack t) = Classic.makeBlack (toKeys t) := by
  cases t with
  | empty => rfl
  | node c l k v r => simp [makeBlack, Classic.makeBlack, toKeys, embedColor]

/-- `toKeys` commutes with Daedalus's unified `balance` unconditionally.

This is the structural heart of the equivalence: Daedalus `balance` and Classic
`balance` produce the same tree structure (modulo the value-stripping embedding).
No invariant constraints are needed because both functions handle all four rotation
cases identically.

The proof case-splits on `c`, `l` (for LL/LR arms), and `r` (for RL/RR arms),
until all discriminants of both `balance` functions are concrete constructors. -/
theorem toKeys_balance {α β : Type} {c : Color} {l : Tree α β}
    {k : α} {v : β} {r : Tree α β} :
    toKeys (balance c l k v r) =
    Classic.balance (embedColor c) (toKeys l) k (toKeys r) := by
  cases c with
  | red => rfl
  | black =>
    cases l with
    | empty =>
      -- No LL/LR. Case-split r for RL/RR.
      cases r with
      | empty => rfl
      | node cr lr _ _ rr => cases cr with
        | black => rfl
        | red => cases lr with
          | empty => cases rr with
            | empty => rfl
            | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl  -- RR
          | node clr _ _ _ _ => cases clr with
            | red => rfl  -- RL
            | black => cases rr with
              | empty => rfl
              | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl  -- RR
    | node cl ll _ _ rl =>
      cases cl with
      | black =>
        -- l is black: no LL/LR. Case-split r.
        cases r with
        | empty => rfl
        | node cr lr _ _ rr => cases cr with
          | black => rfl
          | red => cases lr with
            | empty => cases rr with
              | empty => rfl
              | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
            | node clr _ _ _ _ => cases clr with
              | red => rfl
              | black => cases rr with
                | empty => rfl
                | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
      | red =>
        cases ll with
        | empty =>
          cases rl with
          | empty =>
            -- No LL/LR. Case-split r.
            cases r with
            | empty => rfl
            | node cr lr _ _ rr => cases cr with
              | black => rfl
              | red => cases lr with
                | empty => cases rr with
                  | empty => rfl
                  | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
                | node clr _ _ _ _ => cases clr with
                  | red => rfl
                  | black => cases rr with
                    | empty => rfl
                    | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
          | node crl _ _ _ _ =>
            cases crl with
            | black =>
              -- No LL/LR. Case-split r.
              cases r with
              | empty => rfl
              | node cr lr _ _ rr => cases cr with
                | black => rfl
                | red => cases lr with
                  | empty => cases rr with
                    | empty => rfl
                    | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
                  | node clr _ _ _ _ => cases clr with
                    | red => rfl
                    | black => cases rr with
                      | empty => rfl
                      | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
            | red => rfl  -- LR
        | node cll _ _ _ _ =>
          cases cll with
          | red => rfl  -- LL
          | black =>
            cases rl with
            | empty =>
              -- No LL/LR. Case-split r.
              cases r with
              | empty => rfl
              | node cr lr _ _ rr => cases cr with
                | black => rfl
                | red => cases lr with
                  | empty => cases rr with
                    | empty => rfl
                    | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
                  | node clr _ _ _ _ => cases clr with
                    | red => rfl
                    | black => cases rr with
                      | empty => rfl
                      | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
            | node crl _ _ _ _ =>
              cases crl with
              | black =>
                -- No LL/LR. Case-split r.
                cases r with
                | empty => rfl
                | node cr lr _ _ rr => cases cr with
                  | black => rfl
                  | red => cases lr with
                    | empty => cases rr with
                      | empty => rfl
                      | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
                    | node clr _ _ _ _ => cases clr with
                      | red => rfl
                      | black => cases rr with
                        | empty => rfl
                        | node crr _ _ _ _ => cases crr with | black => rfl | red => rfl
              | red => rfl  -- LR

/-! ### NoRedRed whole-tree invariant

To connect `setRebalanceLeft`/`setRebalanceRight` (which need `NoRedRedChildren`
on the unmodified subtree) with the `toKeys ∘ ins = Classic.ins ∘ toKeys`
equivalence, we need a whole-tree "no red-red violations anywhere" invariant.
This holds for all trees built by `insert` from `empty`. -/

/-- No red-red violations anywhere in the tree: no red node has a red child,
recursively. This is one of the two red-black tree invariants (the other being
uniform black-height). -/
def NoRedRed : Tree α β → Prop
  | empty => True
  | node red (node red _ _ _ _) _ _ _ => False
  | node red _ _ _ (node red _ _ _ _) => False
  | node _ l _ _ r => NoRedRed l ∧ NoRedRed r

/-- A tree with no red-red anywhere has no red-red at the top level. -/
theorem noRedRed_implies_noRedRedChildren {α β : Type} {t : Tree α β}
    (h : NoRedRed t) : NoRedRedChildren t := by
  cases t with
  | empty => trivial
  | node c l _ _ r =>
    cases c with
    | black => simp [NoRedRedChildren]
    | red =>
      cases l with
      | empty =>
        cases r with
        | empty => simp [NoRedRedChildren]
        | node cr _ _ _ _ =>
          cases cr with
          | black => simp [NoRedRedChildren]
          | red => exact absurd h (by simp [NoRedRed])
      | node cl _ _ _ _ =>
        cases cl with
        | red => exact absurd h (by simp [NoRedRed])
        | black =>
          cases r with
          | empty => simp [NoRedRedChildren]
          | node cr _ _ _ _ =>
            cases cr with
            | black => simp [NoRedRedChildren]
            | red => exact absurd h (by simp [NoRedRed])

/-- Extract the NoRedRed property of both children from a parent node. -/
theorem noRedRed_children {α β : Type} {c : Color} {l : Tree α β}
    {k : α} {v : β} {r : Tree α β} (h : NoRedRed (node c l k v r)) :
    NoRedRed l ∧ NoRedRed r := by
  cases c with
  | black => exact h
  | red =>
    cases l with
    | empty =>
      cases r with
      | empty => exact ⟨trivial, trivial⟩
      | node cr _ _ _ _ =>
        cases cr with
        | black => exact ⟨trivial, h.2⟩
        | red => exact absurd h (by simp [NoRedRed])
    | node cl _ _ _ _ =>
      cases cl with
      | red => exact absurd h (by simp [NoRedRed])
      | black =>
        cases r with
        | empty => exact ⟨h.1, trivial⟩
        | node cr _ _ _ _ =>
          cases cr with
          | black => exact h
          | red => exact absurd h (by simp [NoRedRed])

/-- `toKeys` commutes with `setRebalanceLeft` when the right subtree has no
red-red violation. Follows directly from Part A + `toKeys_balance`. -/
theorem toKeys_setRebalanceLeft {α β : Type} [Ord α] {c : Color} {newLeft : Tree α β}
    {k : α} {v : β} {r : Tree α β} (hr : NoRedRedChildren r) :
    toKeys (setRebalanceLeft c newLeft k v r) =
    Classic.balance (embedColor c) (toKeys newLeft) k (toKeys r) := by
  rw [setRebalanceLeft_eq_balance hr, toKeys_balance]

/-- `toKeys` commutes with `setRebalanceRight` when the left subtree has no
red-red violation. Symmetric to `toKeys_setRebalanceLeft`. -/
theorem toKeys_setRebalanceRight {α β : Type} [Ord α] {c : Color} {l : Tree α β}
    {k : α} {v : β} {newRight : Tree α β} (hl : NoRedRedChildren l) :
    toKeys (setRebalanceRight c l k v newRight) =
    Classic.balance (embedColor c) (toKeys l) k (toKeys newRight) := by
  rw [setRebalanceRight_eq_balance hl, toKeys_balance]

/-- `toKeys` commutes with `ins`: inserting into a Daedalus map and then stripping
values produces the same set tree as inserting directly into the Classic set.

Requires `NoRedRed t` to ensure the unmodified subtree at each recursive step
has no red-red violation (needed for the split-rebalance equivalence from Part A).
The value update on equal keys is invisible to `toKeys` since it only preserves
the key structure. -/
theorem toKeys_ins {β : Type} {k : Nat} {v : β} {t : Tree Nat β}
    (h : NoRedRed t) :
    toKeys (ins k v t) = Classic.ins k (toKeys t) := by
  induction t with
  | empty => simp [ins, Classic.ins, toKeys, embedColor]
  | node c l kn vn r ihl ihr =>
    have ⟨hl, hr⟩ := noRedRed_children h
    simp only [ins]
    split
    · -- k < kn: both recurse left, then rebalance
      rename_i hlt
      rw [toKeys_setRebalanceLeft (noRedRed_implies_noRedRedChildren hr), ihl hl]
      simp only [toKeys, embedColor, Classic.ins, hlt]
    · -- k = kn: Daedalus updates value, Classic returns unchanged
      rename_i heq
      simp only [toKeys, embedColor, Classic.ins, heq]
    · -- k > kn: both recurse right, then rebalance
      rename_i hgt
      rw [toKeys_setRebalanceRight (noRedRed_implies_noRedRedChildren hl), ihr hr]
      simp only [toKeys, embedColor, Classic.ins, hgt]

/-- **Main equivalence theorem**: `toKeys` commutes with `insert`.
Daedalus `insert k v t` produces the same key structure as `Classic.insert k`,
for any tree without red-red violations.

Trees built by repeated `insert` from `empty` always satisfy `NoRedRed`
(since `insert` maintains the red-black invariants), so this theorem applies
to all trees arising from normal usage. -/
theorem toKeys_insert {β : Type} {k : Nat} {v : β} {t : Tree Nat β}
    (h : NoRedRed t) :
    toKeys (insert k v t) = Classic.insert k (toKeys t) := by
  unfold insert Classic.insert
  rw [toKeys_makeBlack, toKeys_ins h]

-- ════════════════════════════════════════════════════════════════════════════════
-- Part D: Color invariant preservation — insert preserves NoRedRed
-- ════════════════════════════════════════════════════════════════════════════════

/-- A tree where the children of the root satisfy `NoRedRed`, but the root
itself may have a red-red violation. This captures the output of `ins`
(before `makeBlack` forces the root black). -/
def NearlyNoRedRed : Tree α β → Prop
  | empty => True
  | node _ l _ _ r => NoRedRed l ∧ NoRedRed r

/-- `NoRedRed` implies `NearlyNoRedRed`: if the whole tree is valid,
then certainly the children are valid. -/
theorem noRedRed_implies_nearlyNoRedRed {t : Tree α β}
    (h : NoRedRed t) : NearlyNoRedRed t := by
  cases t with
  | empty => trivial
  | node c l k v r => exact noRedRed_children h

/-- `makeBlack` on a nearly-valid tree produces a fully valid tree.
Since `makeBlack` forces the root black, any red-red violation at the
root (red node with a red child) is eliminated. -/
theorem noRedRed_makeBlack_of_nearly {t : Tree α β}
    (h : NearlyNoRedRed t) : NoRedRed (makeBlack t) := by
  cases t with
  | empty => trivial
  | node c l k v r => exact h

/-- `setRebalanceLeft black` preserves `NoRedRed` when the left child is
nearly valid and the right child is fully valid. The LL and LR rotation
cases rearrange subtrees that are all `NoRedRed` (extracted from
`NearlyNoRedRed`), and default cases pass through since the absence of
a red-red pattern at `nl`'s root plus `NearlyNoRedRed` implies `NoRedRed`. -/
theorem noRedRed_setRebalanceLeft_black {nl : Tree α β}
    {k : α} {v : β} {r : Tree α β}
    (hnl : NearlyNoRedRed nl) (hr : NoRedRed r) :
    NoRedRed (setRebalanceLeft black nl k v r) := by
  cases nl with
  | empty => exact ⟨trivial, hr⟩
  | node cnl ll knl vnl lr =>
    cases cnl with
    | black => exact ⟨hnl, hr⟩
    | red =>
      cases ll with
      | empty =>
        cases lr with
        | empty => exact ⟨⟨trivial, trivial⟩, hr⟩
        | node clr _ _ _ _ =>
          cases clr with
          | black => exact ⟨⟨trivial, hnl.2⟩, hr⟩
          | red => -- LR case
            exact ⟨⟨hnl.1, (noRedRed_children hnl.2).1⟩, ⟨(noRedRed_children hnl.2).2, hr⟩⟩
      | node cll _ _ _ _ =>
        cases cll with
        | red => -- LL case
          exact ⟨noRedRed_children hnl.1, ⟨hnl.2, hr⟩⟩
        | black =>
          cases lr with
          | empty => exact ⟨⟨hnl.1, trivial⟩, hr⟩
          | node clr _ _ _ _ =>
            cases clr with
            | black => exact ⟨⟨hnl.1, hnl.2⟩, hr⟩
            | red => -- LR case
              exact ⟨⟨hnl.1, (noRedRed_children hnl.2).1⟩, ⟨(noRedRed_children hnl.2).2, hr⟩⟩

/-- Symmetric to `noRedRed_setRebalanceLeft_black`. -/
theorem noRedRed_setRebalanceRight_black {l : Tree α β}
    {k : α} {v : β} {nr : Tree α β}
    (hl : NoRedRed l) (hnr : NearlyNoRedRed nr) :
    NoRedRed (setRebalanceRight black l k v nr) := by
  cases nr with
  | empty => exact ⟨hl, trivial⟩
  | node cnr rl knr vnr rr =>
    cases cnr with
    | black => exact ⟨hl, hnr⟩
    | red =>
      cases rl with
      | empty =>
        cases rr with
        | empty => exact ⟨hl, ⟨trivial, trivial⟩⟩
        | node crr _ _ _ _ =>
          cases crr with
          | black => exact ⟨hl, ⟨trivial, hnr.2⟩⟩
          | red => -- RR case
            exact ⟨⟨hl, hnr.1⟩, ⟨(noRedRed_children hnr.2).1, (noRedRed_children hnr.2).2⟩⟩
      | node crl _ _ _ _ =>
        cases crl with
        | red => -- RL case
          exact ⟨⟨hl, (noRedRed_children hnr.1).1⟩, ⟨(noRedRed_children hnr.1).2, hnr.2⟩⟩
        | black =>
          cases rr with
          | empty => exact ⟨hl, ⟨hnr.1, trivial⟩⟩
          | node crr _ _ _ _ =>
            cases crr with
            | black => exact ⟨hl, ⟨hnr.1, hnr.2⟩⟩
            | red => -- RR case
              exact ⟨⟨hl, hnr.1⟩, ⟨(noRedRed_children hnr.2).1, (noRedRed_children hnr.2).2⟩⟩

/-- In a `NoRedRed` tree with a red root, both children have black roots
(or are empty). This is because a red child would create a red-red violation. -/
theorem isBlack_children_of_red {l : Tree α β} {k : α} {v : β} {r : Tree α β}
    (h : NoRedRed (node red l k v r)) : isBlack l = true ∧ isBlack r = true := by
  refine ⟨?_, ?_⟩
  · cases l with
    | empty => rfl
    | node cl _ _ _ _ => cases cl with
      | black => rfl
      | red => exact absurd h (by simp [NoRedRed])
  · cases r with
    | empty => rfl
    | node cr _ _ _ _ => cases cr with
      | black => rfl
      | red =>
        cases l with
        | empty => exact absurd h (by simp [NoRedRed])
        | node cl _ _ _ _ => cases cl with
          | black => exact absurd h (by simp [NoRedRed])
          | red => exact absurd h (by simp [NoRedRed])

/-- Combined result: `ins` on a `NoRedRed` tree produces a `NearlyNoRedRed`
tree, and if the input has a black root (or is empty), the result is fully
`NoRedRed`. The second part is needed when the parent is red: its children
must be black-rooted, so `ins` into them yields a fully valid tree. -/
theorem ins_noRedRed {α β : Type} [Ord α] {k : α} {v : β} {t : Tree α β}
    (h : NoRedRed t) :
    NearlyNoRedRed (ins k v t) ∧ (isBlack t = true → NoRedRed (ins k v t)) := by
  induction t with
  | empty =>
    simp [ins, NearlyNoRedRed, NoRedRed, isBlack]
  | node c l kn vn r ihl ihr =>
    have ⟨hl, hr⟩ := noRedRed_children h
    obtain ⟨ihl1, ihl2⟩ := ihl hl
    obtain ⟨ihr1, ihr2⟩ := ihr hr
    simp only [ins]
    split
    · -- k < kn: setRebalanceLeft c (ins k v l) kn vn r
      constructor
      · -- NearlyNoRedRed
        cases c with
        | black =>
          exact noRedRed_implies_nearlyNoRedRed
            (noRedRed_setRebalanceLeft_black ihl1 hr)
        | red =>
          -- c = red, so l has a black root. Use ihl2 to get full NoRedRed.
          exact ⟨ihl2 (isBlack_children_of_red h).1, hr⟩
      · -- isBlack → NoRedRed
        intro hb
        cases c with
        | black => exact noRedRed_setRebalanceLeft_black ihl1 hr
        | red => simp [isBlack] at hb
    · -- k = kn: node c l kn v r
      exact ⟨⟨hl, hr⟩, fun _ => by cases c with
        | black => exact ⟨hl, hr⟩
        | red => simp [isBlack] at *⟩
    · -- k > kn: setRebalanceRight c l kn vn (ins k v r)
      constructor
      · cases c with
        | black =>
          exact noRedRed_implies_nearlyNoRedRed
            (noRedRed_setRebalanceRight_black hl ihr1)
        | red =>
          exact ⟨hl, ihr2 (isBlack_children_of_red h).2⟩
      · intro hb
        cases c with
        | black => exact noRedRed_setRebalanceRight_black hl ihr1
        | red => simp [isBlack] at hb

/-- **`insert` preserves `NoRedRed`**: inserting into a valid red-black tree
produces a valid red-black tree (with respect to the no-red-red invariant).
Follows from `ins_noRedRed` (ins produces a nearly-valid tree) and
`noRedRed_makeBlack_of_nearly` (makeBlack fixes any root violation). -/
theorem noRedRed_insert {α β : Type} [Ord α] {k : α} {v : β} {t : Tree α β}
    (h : NoRedRed t) : NoRedRed (insert k v t) :=
  noRedRed_makeBlack_of_nearly (ins_noRedRed h).1

-- ════════════════════════════════════════════════════════════════════════════════
-- Part E: Cross-implementation fromList equivalence (capstone theorem)
-- ════════════════════════════════════════════════════════════════════════════════

/-- The empty tree satisfies `NoRedRed`. -/
theorem noRedRed_empty : NoRedRed (α := α) (β := β) empty := trivial

/-- `toKeys` commutes with folding `insert` over a list: the Daedalus foldl
matches the Classic foldl on the key projection. Generalizes over the
accumulator tree `t` (which must satisfy `NoRedRed`). -/
private theorem toKeys_foldl {β : Type} (kvs : List (Nat × β))
    (t : Tree Nat β) (ht : NoRedRed t) :
    toKeys (kvs.foldl (fun t (k, v) => insert k v t) t) =
    (kvs.map Prod.fst).foldl (fun t x => Classic.insert x t) (toKeys t) := by
  induction kvs generalizing t with
  | nil => rfl
  | cons kv kvs ih =>
    simp only [List.foldl, List.map]
    rw [ih _ (noRedRed_insert ht), toKeys_insert ht]

/-- **Capstone theorem**: building a Daedalus map from a key-value list and
projecting to keys produces the same tree as building a Classic set from the
keys directly. This is the end-to-end structural equivalence. -/
theorem toKeys_fromList {β : Type} (kvs : List (Nat × β)) :
    toKeys (fromList kvs) = Classic.fromList (kvs.map Prod.fst) := by
  simp only [fromList, Classic.fromList]
  exact toKeys_foldl kvs empty noRedRed_empty

/-- Corollary: the sorted key lists are identical. -/
theorem toKeys_fromList_equiv {β : Type} (kvs : List (Nat × β)) :
    Classic.toList (toKeys (fromList kvs)) =
    Classic.toList (Classic.fromList (kvs.map Prod.fst)) := by
  rw [toKeys_fromList]

/-- `findNode` on a Daedalus tree agrees with `contains` on its key projection:
`contains` returns `true` exactly when `findNode` returns `some`.

No `NoRedRed` or `IsBST` hypothesis is needed — this is purely structural,
following from the fact that both functions branch on `compare` at each node
and `toKeys` preserves every key. -/
theorem contains_toKeys_eq_findNode_isSome [Ord α] {k : α} {t : Tree α β} :
    Classic.contains k (toKeys t) = (findNode k t).isSome := by
  induction t with
  | empty => rfl
  | node c l kn vn r ihl ihr =>
    simp only [findNode, toKeys, Classic.contains]
    cases compare k kn with
    | lt => exact ihl
    | eq => rfl
    | gt => exact ihr

end RBTree.Daedalus
