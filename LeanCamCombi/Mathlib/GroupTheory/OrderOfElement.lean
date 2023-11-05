import Mathlib.GroupTheory.OrderOfElement

--TODO: Turn `is_of_fin_order_iff_coe` around. Rename to `subgroup.is_of_fin_order_coe`
--TODO: Turn `is_of_fin_order_iff_coe` around. Rename to `subgroup.is_of_fin_order_coe`
open Function Set Subgroup Submonoid

section Monoid

variable {α : Type*} [Monoid α] {a : α}

-- --TODO: Fix name `order_eq_card_zpowers` to `order_of_eq_card_zpowers`
-- /-- See also `order_eq_card_powers`. -/
-- @[to_additive add_order_eq_card_multiples' "See also `add_order_eq_card_multiples`."]
-- lemma order_of_eq_card_powers' : order_of a = nat.card (powers a) := sorry
-- @[to_additive is_of_fin_add_order.finite_multiples]
-- lemma is_of_fin_order.finite_powers (h : is_of_fin_order a) : (powers a : set α).finite :=
-- begin
--   rw [←order_of_pos_iff, order_of_eq_card_powers'] at h,
--   exact finite_coe_iff.1 (nat.finite_of_card_ne_zero h.ne'),
-- end
end Monoid
