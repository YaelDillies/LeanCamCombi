import Mathlib.Data.ZMod.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import LeanCamCombi.Mathlib.GroupTheory.Subgroup.Basic

open Function Set Subgroup Submonoid

variable {α : Type*}

section Group
variable [Group α] {s : Subgroup α} (a : α)

/-- See also `order_eq_card_zpowers`. -/
@[to_additive (attr := simp) Nat.card_zmultiples "See also `add_order_eq_card_zmultiples`."]
lemma Nat.card_zpowers : Nat.card (zpowers a) = orderOf a := by
  have := Nat.card_congr (MulAction.orbitZpowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this

variable {a}

@[to_additive (attr := simp) finite_zmultiples]
lemma finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrder a := by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, Subgroup.nonempty, true_and]

@[to_additive (attr := simp) infinite_zmultiples]
lemma infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a := finite_zpowers.not

@[to_additive IsOfFinAddOrder.finite_zmultiples']
protected alias ⟨_, IsOfFinOrder.finite_zpowers'⟩ := finite_zpowers

@[to_additive]
lemma orderOf_le_card_subgroup (hs : (s : Set α).Finite) (ha : a ∈ s) : orderOf a ≤ Nat.card s := by
  rw [← Nat.card_zpowers]; exact Nat.card_mono hs (zpowers_le.2 ha)

end Group
