import Mathlib.Algebra.GroupWithZero.Units.Lemmas

section
variable {α : Type*} [CommGroupWithZero α] {a b : α}

lemma div_mul_cancel''₀ (ha : a ≠ 0) (b : α) : a / (a * b) = b⁻¹ := by
  rw [div_mul_eq_div_div, div_self ha, one_div]

end
