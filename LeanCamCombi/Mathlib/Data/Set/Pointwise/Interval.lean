import Mathlib.Data.Set.Pointwise.Interval

open scoped Pointwise

namespace Set
variable {α : Type*} [OrderedCommGroup α]

@[to_additive (attr := simp)]
lemma inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹ := by ext; simp [le_inv', inv_le', and_comm]

end Set
