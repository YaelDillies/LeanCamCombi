import Mathlib.Algebra.MvPolynomial.Equiv

namespace MvPolynomial
variable {R σ : Type*} [CommSemiring R] [IsEmpty σ]

@[simp] lemma isEmptyRingEquiv_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = C := rfl
@[simp] lemma isEmptyRingEquiv_symm_apply (r : R) : (isEmptyRingEquiv R σ).symm r = C r := rfl

lemma isEmptyRingEquiv_eq_coeff_zero {σ R : Type*} [CommSemiring R] [IsEmpty σ] {x} :
    isEmptyRingEquiv R σ x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := (isEmptyRingEquiv R σ).symm.surjective x
  simp

noncomputable
def commAlgEquiv (R S₁ S₂ : Type*) [CommSemiring R] :
    MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (MvPolynomial S₁ R) :=
  (sumAlgEquiv R S₁ S₂).symm.trans ((renameEquiv _ (.sumComm S₁ S₂)).trans (sumAlgEquiv R S₂ S₁))

lemma commAlgEquiv_C {R S₁ S₂ : Type*} [CommSemiring R] (p) :
    commAlgEquiv R S₁ S₂ (.C p) = .map C p := by
  suffices (commAlgEquiv R S₁ S₂).toAlgHom.comp
      (IsScalarTower.toAlgHom R (MvPolynomial S₂ R) _) = mapAlgHom (Algebra.ofId _ _) by
    exact DFunLike.congr_fun this p
  ext x : 1
  simp [commAlgEquiv]

lemma commAlgEquiv_C_X {R S₁ S₂ : Type*} [CommSemiring R] (i) :
    commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i := by simp [commAlgEquiv_C]

lemma commAlgEquiv_X {R S₁ S₂ : Type*} [CommSemiring R] (i) :
    commAlgEquiv R S₁ S₂ (.X i) = .C (.X i) := by simp [commAlgEquiv]

end MvPolynomial
