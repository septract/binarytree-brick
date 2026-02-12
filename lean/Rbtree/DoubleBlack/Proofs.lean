import Rbtree.DoubleBlack

/-!
# BST Proofs for the DoubleBlack Red-Black Tree

Proves that `insert` (and partially `delete`) preserve the BST ordering invariant
for the 4-color DoubleBlack implementation. The insertion proofs mirror the Classic
proofs since `balanceCore` has the same structure as `Classic.balance`.
-/

namespace RBTree.DoubleBlack

open Color Tree

/-- Every value stored in the tree satisfies predicate `p`. -/
def ForAll (p : α → Prop) : Tree α → Prop
  | leaf => True
  | doubleBlackLeaf => True
  | node _ l v r => ForAll p l ∧ p v ∧ ForAll p r

/-- The BST ordering invariant. -/
def IsBST : Tree Nat → Prop
  | leaf => True
  | doubleBlackLeaf => True
  | node _ l v r =>
    IsBST l ∧ IsBST r ∧ ForAll (· < v) l ∧ ForAll (v < ·) r

/-- No transient colors remain (the tree uses only red/black). -/
def IsStandard : Tree α → Prop
  | leaf => True
  | doubleBlackLeaf => False
  | node c l _ r =>
    c ≠ doubleBlack ∧ c ≠ negativeBlack ∧ IsStandard l ∧ IsStandard r

section NatProofs

-- ════════════════════════════════════════════════════════════════════════════════
-- Weakening lemmas
-- ════════════════════════════════════════════════════════════════════════════════

theorem forAll_lt_weaken {v w : Nat} {t : Tree Nat} (hvw : v < w)
    (h : ForAll (· < v) t) : ForAll (· < w) t := by
  induction t with
  | leaf => trivial
  | doubleBlackLeaf => trivial
  | node _ l x r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans h.2.1 hvw, ihr h.2.2⟩

theorem forAll_gt_weaken {v w : Nat} {t : Tree Nat} (hwv : w < v)
    (h : ForAll (v < ·) t) : ForAll (w < ·) t := by
  induction t with
  | leaf => trivial
  | doubleBlackLeaf => trivial
  | node _ l x r ihl ihr =>
    simp only [ForAll] at h ⊢
    exact ⟨ihl h.1, Nat.lt_trans hwv h.2.1, ihr h.2.2⟩

-- ════════════════════════════════════════════════════════════════════════════════
-- balanceCore proofs (mirrors Classic.balance proofs exactly)
-- ════════════════════════════════════════════════════════════════════════════════

theorem forAll_balanceCore {p : Nat → Prop} {c l v r} :
    ForAll p l → p v → ForAll p r → ForAll p (balanceCore c l v r) := by
  intro hl hv hr
  unfold balanceCore
  split <;> simp_all [ForAll]

theorem isBST_balanceCore {c l v r} :
    IsBST l → IsBST r →
    ForAll (· < v) l → ForAll (v < ·) r →
    IsBST (balanceCore c l v r) := by
  intro hl hr hltl hltr
  unfold balanceCore
  split
  · -- Left-left rotation
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
  · -- Left-right rotation
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
  · -- Right-left rotation
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
  · -- Right-right rotation
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

-- ════════════════════════════════════════════════════════════════════════════════
-- Full balance proofs (adds NB cases, delegates to balanceCore)
-- ════════════════════════════════════════════════════════════════════════════════

theorem forAll_balance {p : Nat → Prop} {c l v r} :
    ForAll p l → p v → ForAll p r → ForAll p (balance c l v r) := by
  intro hl hv hr
  unfold balance
  split
  · -- NB left child
    simp only [ForAll] at hl hr ⊢
    exact ⟨forAll_balanceCore hl.1 hl.2.1 hl.2.2, hv, hr.1, hr.2.1, hr.2.2⟩
  · -- NB right child
    simp only [ForAll] at hl hr ⊢
    exact ⟨hl, hv, forAll_balanceCore hr.1 hr.2.1 hr.2.2⟩
  · -- Delegate to balanceCore
    exact forAll_balanceCore hl hv hr

theorem isBST_balance {c l v r} :
    IsBST l → IsBST r →
    ForAll (· < v) l → ForAll (v < ·) r →
    IsBST (balance c l v r) := by
  intro hl hr hltl hltr
  unfold balance
  split
  · -- NB left: doubleBlack parent, negativeBlack left child
    simp only [IsBST, ForAll] at *
    exact ⟨isBST_balanceCore hl.1 hl.2.1 hl.2.2.1 hl.2.2.2,
           hr,
           forAll_balanceCore hltl.1 hltl.2.1 hltl.2.2,
           hltr⟩
  · -- NB right: doubleBlack parent, negativeBlack right child
    simp only [IsBST, ForAll] at *
    exact ⟨hl,
           isBST_balanceCore hr.1 hr.2.1 hr.2.2.1 hr.2.2.2,
           hltl,
           forAll_balanceCore hltr.1 hltr.2.1 hltr.2.2⟩
  · -- Delegate to balanceCore
    exact isBST_balanceCore hl hr hltl hltr

-- ════════════════════════════════════════════════════════════════════════════════
-- Insertion proofs
-- ════════════════════════════════════════════════════════════════════════════════

theorem forAll_lt_ins {x v : Nat} {t : Tree Nat} (hxv : x < v)
    (h : ForAll (· < v) t) : ForAll (· < v) (ins x t) := by
  induction t with
  | leaf => simp [ins, ForAll]; exact hxv
  | doubleBlackLeaf => simp [ins, ForAll]; exact hxv
  | node c l w r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hw, hr⟩ := h
    unfold ins; split
    · exact forAll_balance (ihl hl) hw hr
    · simp [ForAll]; exact ⟨hl, hw, hr⟩
    · exact forAll_balance hl hw (ihr hr)

theorem forAll_gt_ins {x v : Nat} {t : Tree Nat} (hvx : v < x)
    (h : ForAll (v < ·) t) : ForAll (v < ·) (ins x t) := by
  induction t with
  | leaf => simp [ins, ForAll]; exact hvx
  | doubleBlackLeaf => simp [ins, ForAll]; exact hvx
  | node c l w r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hw, hr⟩ := h
    unfold ins; split
    · exact forAll_balance (ihl hl) hw hr
    · simp [ForAll]; exact ⟨hl, hw, hr⟩
    · exact forAll_balance hl hw (ihr hr)

theorem isBST_ins {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (ins x t) := by
  induction t with
  | leaf => simp [ins, IsBST, ForAll]
  | doubleBlackLeaf => simp [ins, IsBST, ForAll]
  | node c l v r ihl ihr =>
    simp only [IsBST] at h
    obtain ⟨hl, hr, hltl, hltr⟩ := h
    unfold ins; split
    · rename_i hlt; rw [Nat.compare_eq_lt] at hlt
      exact isBST_balance (ihl hl) hr (forAll_lt_ins hlt hltl) hltr
    · exact ⟨hl, hr, hltl, hltr⟩
    · rename_i hgt; rw [Nat.compare_eq_gt] at hgt
      exact isBST_balance hl (ihr hr) hltl (forAll_gt_ins hgt hltr)

theorem isBST_makeBlack {t : Tree Nat} (h : IsBST t) : IsBST (makeBlack t) := by
  unfold makeBlack; split
  · simp only [IsBST] at h; exact h
  · trivial
  · trivial

/-- **Main theorem**: `insert` preserves the BST ordering invariant. -/
theorem isBST_insert {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (insert x t) :=
  isBST_makeBlack (isBST_ins h)

-- ════════════════════════════════════════════════════════════════════════════════
-- Deletion proofs (partial — BST preservation)
-- ════════════════════════════════════════════════════════════════════════════════

theorem forAll_decBlack {p : Nat → Prop} {t : Tree Nat}
    (h : ForAll p t) : ForAll p t.decBlack := by
  cases t with
  | leaf => trivial
  | doubleBlackLeaf => trivial
  | node c l v r => simp only [Tree.decBlack, ForAll] at *; exact h

theorem isBST_decBlack {t : Tree Nat}
    (h : IsBST t) : IsBST t.decBlack := by
  cases t with
  | leaf => trivial
  | doubleBlackLeaf => trivial
  | node c l v r => simp only [Tree.decBlack, IsBST] at *; exact h

theorem forAll_bubble {p : Nat → Prop} {c l v r} :
    ForAll p l → p v → ForAll p r → ForAll p (bubble c l v r) := by
  intro hl hv hr
  unfold bubble
  split
  · exact forAll_balance (forAll_decBlack hl) hv (forAll_decBlack hr)
  · simp [ForAll]; exact ⟨hl, hv, hr⟩

theorem isBST_bubble {c l v r} :
    IsBST l → IsBST r →
    ForAll (· < v) l → ForAll (v < ·) r →
    IsBST (bubble c l v r) := by
  intro hl hr hltl hltr
  unfold bubble
  split
  · exact isBST_balance (isBST_decBlack hl) (isBST_decBlack hr)
      (forAll_decBlack hltl) (forAll_decBlack hltr)
  · exact ⟨hl, hr, hltl, hltr⟩

private theorem forAll_makeBlack' {p : Nat → Prop} {t : Tree Nat}
    (h : ForAll p t) : ForAll p (makeBlack t) := by
  cases t with
  | leaf => trivial
  | doubleBlackLeaf => trivial
  | node c l v r => simp only [makeBlack, ForAll] at *; exact h

theorem forAll_removeMax {p : Nat → Prop} {t : Tree Nat} {m t'}
    (h : ForAll p t) (heq : removeMax t = some (m, t')) :
    p m ∧ ForAll p t' := by
  induction t generalizing m t' with
  | leaf => simp [removeMax] at heq
  | doubleBlackLeaf => simp [removeMax] at heq
  | node c l v r _ ihr =>
    simp only [ForAll] at h
    cases r with
    | leaf =>
      simp only [removeMax, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine ⟨h.2.1, ?_⟩
      split
      · trivial
      · exact forAll_makeBlack' h.1
      · exact h.1
    | doubleBlackLeaf =>
      simp only [removeMax] at heq
      -- removeMax doubleBlackLeaf = none, so match falls to the none branch
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨h.2.1, h.1⟩
    | node cr lr vr rr =>
      simp only [removeMax] at heq
      cases hrm : removeMax (node cr lr vr rr) with
      | none =>
        simp only [hrm, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨h.2.1, h.1⟩
      | some val =>
        simp only [hrm, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have := ihr h.2.2 hrm
        exact ⟨this.1, forAll_bubble h.1 h.2.1 this.2⟩

theorem removeMax_lt {t : Tree Nat} {m t' v}
    (h : ForAll (· < v) t) (heq : removeMax t = some (m, t')) :
    m < v ∧ ForAll (· < v) t' := by
  exact forAll_removeMax h heq

theorem isBST_removeMax {t : Tree Nat} {m t'}
    (h : IsBST t) (heq : removeMax t = some (m, t')) :
    IsBST t' := by
  induction t generalizing m t' with
  | leaf => simp [removeMax] at heq
  | doubleBlackLeaf => simp [removeMax] at heq
  | node c l v r _ ihr =>
    simp only [IsBST] at h
    cases r with
    | leaf =>
      simp only [removeMax, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      split
      · trivial
      · exact isBST_makeBlack h.1
      · exact h.1
    | doubleBlackLeaf =>
      simp only [removeMax] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact h.1
    | node cr lr vr rr =>
      simp only [removeMax] at heq
      cases hrm : removeMax (node cr lr vr rr) with
      | none =>
        simp only [hrm, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact h.1
      | some val =>
        simp only [hrm, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have isBSTr' := ihr h.2.1 hrm
        have hgtr' := (forAll_removeMax h.2.2.2 hrm).2
        exact isBST_bubble h.1 isBSTr' h.2.2.1 hgtr'

theorem removeMax_isBST_bound {t : Tree Nat} {m t'}
    (hbst : IsBST t) (heq : removeMax t = some (m, t')) :
    ForAll (· < m) t' := by
  induction t generalizing m t' with
  | leaf => simp [removeMax] at heq
  | doubleBlackLeaf => simp [removeMax] at heq
  | node c l v r _ ihr =>
    simp only [IsBST] at hbst
    cases r with
    | leaf =>
      simp only [removeMax, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- m = v, t' depends on c and l
      split
      · trivial
      · exact forAll_makeBlack' hbst.2.2.1
      · exact hbst.2.2.1
    | doubleBlackLeaf =>
      simp only [removeMax] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hbst.2.2.1
    | node cr lr vr rr =>
      simp only [removeMax] at heq
      cases hrm : removeMax (node cr lr vr rr) with
      | none =>
        simp only [hrm, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact hbst.2.2.1
      | some val =>
        simp only [hrm, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hvm : v < val.1 := (forAll_removeMax hbst.2.2.2 hrm).1
        have hlm : ForAll (· < val.1) l := forAll_lt_weaken hvm hbst.2.2.1
        have hr'm : ForAll (· < val.1) val.2 := ihr hbst.2.1 hrm
        exact forAll_bubble hlm hvm hr'm

theorem forAll_del {p : Nat → Prop} {x : Nat} {t : Tree Nat}
    (h : ForAll p t) : ForAll p (del x t) := by
  induction t with
  | leaf => exact h
  | doubleBlackLeaf => exact h
  | node c l v r ihl ihr =>
    simp only [ForAll] at h
    obtain ⟨hl, hv, hr⟩ := h
    unfold del; split
    · -- x < v
      exact forAll_bubble (ihl hl) hv hr
    · -- x > v
      exact forAll_bubble hl hv (ihr hr)
    · -- x = v
      split
      · -- leaf, leaf
        split <;> trivial
      · -- leaf, r (r ≠ leaf)
        split
        · exact forAll_makeBlack' hr
        · exact hr
      · -- l (l ≠ leaf), leaf
        split
        · exact forAll_makeBlack' hl
        · exact hl
      · -- l, r both non-leaf: use removeMax l
        split
        · rename_i heq
          have := forAll_removeMax hl heq
          exact forAll_bubble this.2 this.1 hr
        · simp [ForAll]; exact ⟨hl, hv, hr⟩

theorem isBST_del {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (del x t) := by
  induction t with
  | leaf => exact h
  | doubleBlackLeaf => exact h
  | node c l v r ihl ihr =>
    simp only [IsBST] at h
    obtain ⟨hl, hr, hltl, hltr⟩ := h
    unfold del; split
    · -- x < v
      rename_i hlt; rw [Nat.compare_eq_lt] at hlt
      exact isBST_bubble (ihl hl) hr (forAll_del hltl) hltr
    · -- x > v
      rename_i hgt; rw [Nat.compare_eq_gt] at hgt
      exact isBST_bubble hl (ihr hr) hltl (forAll_del hltr)
    · -- x = v
      split
      · -- leaf, leaf
        split <;> trivial
      · -- leaf, r (r ≠ leaf)
        split
        · exact isBST_makeBlack hr
        · exact hr
      · -- l (l ≠ leaf), leaf
        split
        · exact isBST_makeBlack hl
        · exact hl
      · -- l, r both non-leaf: use removeMax l
        split
        · rename_i heq
          have hpredv := (forAll_removeMax hltl heq).1
          have isBSTl' := isBST_removeMax hl heq
          have hbound := removeMax_isBST_bound hl heq
          have hpredR := forAll_gt_weaken hpredv hltr
          exact isBST_bubble isBSTl' hr hbound hpredR
        · exact ⟨hl, hr, hltl, hltr⟩

/-- **Main theorem**: `delete` preserves the BST ordering invariant. -/
theorem isBST_delete {x : Nat} {t : Tree Nat} (h : IsBST t) : IsBST (delete x t) :=
  isBST_makeBlack (isBST_del h)

end NatProofs

end RBTree.DoubleBlack
