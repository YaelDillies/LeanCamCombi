import Mathlib.Algebra.Order.Ring.Canonical

section
variable {α : Type*} [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)]
  [ContravariantClass α α (· + ·) (· ≤ ·)]

lemma mul_tsub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
lemma tsub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end
