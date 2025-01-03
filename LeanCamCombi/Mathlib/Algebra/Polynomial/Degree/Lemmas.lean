import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial
variable {R : Type*} [CommRing R]

lemma degree_C_mul_of_mul_ne_zero {r : R} {p : R[X]} (h : r * p.leadingCoeff ≠ 0) :
    (C r * p).degree = p.degree := by
  rw [degree_mul' (by simpa)]; simp [left_ne_zero_of_mul h]

end Polynomial
