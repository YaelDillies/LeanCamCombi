import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial
variable {R : Type*} [CommRing R]

lemma monic_unit_leadingCoeff_inv_smul (p : R[X]) (h : IsUnit p.leadingCoeff) :
    (C ((h.unit⁻¹ : Rˣ) : R) * p).Monic := by
  nontriviality R
  rw [Monic.def, ← coeff_natDegree, natDegree_C_mul_eq_of_mul_ne_zero, coeff_C_mul,
    coeff_natDegree, IsUnit.val_inv_mul]
  rw [IsUnit.val_inv_mul]
  exact one_ne_zero

lemma degree_C_mul_eq_of_mul_ne_zero (r : R) (p : R[X]) (h : r * p.leadingCoeff ≠ 0) :
    (C r * p).degree = p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [degree_eq_natDegree hp, degree_eq_natDegree, natDegree_C_mul_eq_of_mul_ne_zero h]
  exact fun e ↦ h (by simpa using congr(($e).coeff p.natDegree))

end Polynomial
