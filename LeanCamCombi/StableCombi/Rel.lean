import Mathlib.Algebra.Group.Nat.Basic

/-!
# Stable binary relations
-/

variable {α β : Type*} {n : ℕ} {r : α → β → Prop}

def IsOrderPropRelWith (n : ℕ) (r : α → β → Prop) : Prop :=
  ∃ (a : Fin n → α) (b : Fin n → β), ∀ i j, i ≤ j ↔ r (a i) (b j)

def IsOrderPropRel (r : α → β → Prop) : Prop :=
  ∃ (a : ℕ → α) (b : ℕ → β), ∀ i j, i ≤ j ↔ r (a i) (b j)

def IsStableRelWith (n : ℕ) (r : α → β → Prop) : Prop :=
  ∀ (a : Fin n → α) (b : Fin n → β), ∃ i j, ¬ (i ≤ j ↔ r (a i) (b j))

def IsStableRel (r : α → β → Prop) : Prop :=
  ∀ (a : ℕ → α) (b : ℕ → β), ∃ i j, ¬ (i ≤ j ↔ r (a i) (b j))

def IsTreeBoundedRelWith (n : ℕ) (r : α → β → Prop) : Prop :=
  ∀ (a : Vector Bool n → α) (b : ∀ m < n, Vector Bool m → β),
    ∃ (i : Vector Bool n) (m : ℕ) (hmn : m < n) (j : Vector Bool m),
      i.toList <+: j.toList ∧ ¬ (true :: i.toList <+: j.toList ↔ r (a i) (b m hmn j))

@[simp] lemma not_isStableRelWith : ¬ IsStableRelWith n r ↔ IsOrderPropRelWith n r := by
  simp [IsOrderPropRelWith, IsStableRelWith]

@[simp] lemma not_isOrderPropRelWith : ¬ IsOrderPropRelWith n r ↔ IsStableRelWith n r := by
  simp [← not_isStableRelWith]

@[simp] lemma not_isStableRel : ¬ IsStableRel r ↔ IsOrderPropRel r := by
  simp [IsOrderPropRel, IsStableRel]

@[simp] lemma not_isOrderPropRel : ¬ IsOrderPropRel r ↔ IsStableRel r := by simp [← not_isStableRel]

lemma IsStableRelWith.isTreeBoundedRelWith (hr : IsStableRelWith n r) :
    IsTreeBoundedRelWith (2 ^ n + 1) r := sorry

lemma IsTreeBoundedRelWith.isStableRelWith (hr : IsTreeBoundedRelWith n r) :
    IsStableRelWith (2 ^ n) r := sorry
