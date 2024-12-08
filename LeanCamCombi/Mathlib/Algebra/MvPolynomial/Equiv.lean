import Mathlib.Algebra.MvPolynomial.Equiv

namespace MvPolynomial
variable {R σ : Type*} [CommSemiring R] [IsEmpty σ]

@[simp] lemma isEmptyRingEquiv_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = C := rfl
@[simp] lemma isEmptyRingEquiv_symm_apply (r : R) : (isEmptyRingEquiv R σ).symm r = C r := rfl

-- TODO: replace `isEmptyRingEquiv_apply`
lemma isEmptyRingEquiv_apply' (x : MvPolynomial σ R) : isEmptyRingEquiv R σ x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := (isEmptyRingEquiv R σ).symm.surjective x; simp

end MvPolynomial
