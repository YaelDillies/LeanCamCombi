import Mathlib.GroupTheory.OrderOfElement
import LeanCamCombi.Mathlib.Data.Set.Finite
import LeanCamCombi.Mathlib.SetTheory.Cardinal.Finite

--TODO: Turn `isOfFinOrder_iff_coe` around. Rename to `Subgroup.isOfFinOrder_coe`
--TODO: Turn `isOfFinOrder_iff_coe` around. Rename to `Subgroup.isOfFinOrder_coe`
open Function Set Subgroup Submonoid

variable {α : Type*}

section Monoid
variable [Monoid α] {a : α}

-- TODO: Rename `orderOf_pos` to `orderOf_pos_of_finite`, or even delete it
-- TODO: Replace `pow_eq_mod_orderOf`

@[to_additive (attr := simp)]
lemma pow_mod_orderOf (a : α) (n : ℕ) : a ^ (n % orderOf a) = a ^ n := pow_eq_mod_orderOf.symm

@[to_additive] protected lemma IsOfFinOrder.orderOf_pos (ha : IsOfFinOrder a) : 0 < orderOf a :=
  pos_iff_ne_zero.2 $ orderOf_eq_zero_iff.not_left.2 ha

@[to_additive IsOfFinAddOrder.card_multiples_le_addOrderOf]
lemma IsOfFinOrder.card_powers_le_orderOf (ha : IsOfFinOrder a) :
    Nat.card (powers a : Set α) ≤ orderOf a := by
  rw [←Fintype.card_fin (orderOf a), ←Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_surjective (fun n ↦ ⟨a ^ (n : ℕ), by simp [mem_powers_iff]⟩) ?_
  rintro ⟨b, n, rfl⟩
  exact ⟨⟨n % orderOf a, Nat.mod_lt _ ha.orderOf_pos⟩, by simp⟩

@[to_additive IsOfFinAddOrder.finite_multiples]
lemma IsOfFinOrder.finite_powers (ha : IsOfFinOrder a) : (powers a : Set α).Finite := by
  refine Set.Finite.of_surjOn (fun n ↦ a ^ n) ?_ (finite_Iio $ orderOf a)
  rintro _ ⟨n, _, rfl⟩
  exact ⟨n % orderOf a, Nat.mod_lt _ ha.orderOf_pos, by simp⟩

end Monoid

section LeftCancelMonoid
variable [LeftCancelMonoid α] {a : α}

@[to_additive (attr := simp) finite_multiples]
lemma finite_powers : (powers a : Set α).Finite ↔ IsOfFinOrder a := by
  refine ⟨fun h ↦ ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ ↦ a ^ n)
    (fun n ↦ by simp [mem_powers_iff])
  refine (isOfFinOrder_iff_pow_eq_one _).2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  rw [←mul_left_cancel_iff (a := a ^ m), ←pow_add, add_tsub_cancel_of_le hmn.le, ha, mul_one]

@[to_additive (attr := simp) infinite_multiples]
lemma infinite_powers : (powers a : Set α).Infinite ↔ ¬ IsOfFinOrder a := finite_powers.not

--TODO: Fix name `order_eq_card_zpowers` to `orderOf_eq_card_zpowers`
--TODO: Rename ``
/-- See also `orderOf_eq_card_powers`. -/
@[to_additive Nat.card_addSubmonoidMultiples "See also `addOrder_eq_card_multiples`."]
lemma Nat.card_submonoidPowers : Nat.card (powers a) = orderOf a := by
  by_cases ha : IsOfFinOrder a
  · symm
    trans Nat.card (Fin (orderOf a))
    · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    refine Nat.card_eq_of_bijective (fun n ↦ ⟨a ^ (n : ℕ), by simp [mem_powers_iff]⟩) ⟨?_, ?_⟩
    · rintro m n hmn
      simp [pow_eq_pow_iff_modEq] at hmn
      exact Fin.ext $ hmn.eq_of_lt_of_lt m.2 n.2
    · rintro ⟨b, n, rfl⟩
      exact ⟨⟨n % orderOf a, Nat.mod_lt _ ha.orderOf_pos⟩, by simp⟩
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha, Nat.card_eq_zero_of_infinite]

end LeftCancelMonoid
