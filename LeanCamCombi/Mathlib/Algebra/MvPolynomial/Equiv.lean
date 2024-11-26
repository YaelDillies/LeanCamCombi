import Mathlib.Algebra.MvPolynomial.Equiv

namespace MvPolynomial
variable {R σ : Type*} [CommSemiring R] [IsEmpty σ]

@[simp] lemma isEmptyRingEquiv_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = C := rfl
@[simp] lemma isEmptyRingEquiv_symm_apply (r : R) : (isEmptyRingEquiv R σ).symm r = C r := rfl
