import Mathlib.Data.ZMod.Quotient
import LeanCamCombi.Mathlib.SetTheory.Cardinal.Finite

open Function Set Subgroup Submonoid

variable {α : Type*}

section LeftCancelMonoid
variable [LeftCancelMonoid α] {a : α}

-- @[to_additive (attr := simp) finite_multiples] lemma finite_powers :
--   (powers a : set α).finite ↔ is_of_fin_order a :=
-- ⟨λ h, of_not_not $ λ h', infinite_range_of_injective (injective_pow_iff_not_is_of_fin_order.2 h')
--   h, is_of_fin_order.finite_powers⟩
-- @[to_additive (attr := simp) infinite_zmultiples] lemma infinite_powers :
--   (powers a : set α).infinite ↔ ¬ is_of_fin_order a :=
-- finite_powers.not

end LeftCancelMonoid

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
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos, ← SetLike.coe_sort_coe,
    Set.nonempty_of_nonempty_subtype, Nat.card_pos_iff, Set.finite_coe_iff]
  sorry

@[to_additive (attr := simp) infinite_zmultiples]
lemma infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a := finite_zpowers.not

@[to_additive IsOfFinAddOrder.finite_zmultiples']
protected alias ⟨_, IsOfFinOrder.finite_zpowers'⟩ := finite_zpowers

@[to_additive add_order_of_le_card]
lemma orderOf_le_card (hs : (s : Set α).Finite) (ha : a ∈ s) : orderOf a ≤ Nat.card s := by
  rw [← Nat.card_zpowers]; exact Nat.card_mono hs (zpowers_le.2 ha)

end Group
