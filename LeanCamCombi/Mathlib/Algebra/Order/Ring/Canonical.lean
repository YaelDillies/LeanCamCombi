import Mathlib.Algebra.Order.Ring.Canonical

section
variable {α : Type*} [CanonicallyOrderedCommSemiring α] [PosMulStrictMono α] [MulPosStrictMono α]
  {a b c d : α}

--TODO: Fix implicitness of `eq_zero_or_pos`
lemma mul_lt_mul_of_lt_of_lt'' (hab : a < b) (hcd : c < d) : a * c < b * d := by
  obtain rfl | hc := @eq_zero_or_pos _ _ c
  · rw [MulZeroClass.mul_zero]
    exact mul_pos ((zero_le _).trans_lt hab) hcd
  · exact mul_lt_mul_of_lt_of_lt' hab hcd ((zero_le _).trans_lt hab) hc

end
