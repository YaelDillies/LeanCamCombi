import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.LocallyFinite.Basic

open scoped BigOperators

variable {α β : Type*} [PartialOrder α] [CommMonoid β] {f : α → β} {a b : α}

namespace Finset
section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[to_additive]
lemma mul_prod_Ico (h : a ≤ b) : f b * ∏ x in Ico a b, f x = ∏ x in Icc a b, f x := by
  rw [Icc_eq_cons_Ico h, prod_cons]

@[to_additive]
lemma mul_prod_Ioc (h : a ≤ b) : f a * ∏ x in Ioc a b, f x = ∏ x in Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_additive]
lemma mul_prod_Ioi (a : α) : f a * ∏ x in Ioi a, f x = ∏ x in Ici a, f x := by
  rw [Ici_eq_cons_Ioi, prod_cons]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
lemma mul_prod_Iio (a : α) : f a * ∏ x in Iio a, f x = ∏ x in Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

end LocallyFiniteOrderBot
end Finset
