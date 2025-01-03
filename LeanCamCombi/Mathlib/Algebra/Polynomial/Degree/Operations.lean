import Mathlib.Algebra.Polynomial.Degree.Operations

namespace Polynomial
variable {R : Type*} [Semiring R] {a : R}

lemma leadingCoeff_C_mul (ha : IsUnit a) (p : R[X]) :
    (C a * p).leadingCoeff = a * p.leadingCoeff := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [leadingCoeff_mul', leadingCoeff_C]
    simpa [ha.mul_right_eq_zero]
