import Mathlib.Algebra.MvPolynomial.Basic

namespace Submodule
variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

section Module
variable [Module R S] {M N : Submodule R S} {x : MvPolynomial σ S}

variable (σ M)
@[simps]
def mvPolynomial : Submodule R (MvPolynomial σ S) where
  carrier := {p | ∀ i, p.coeff i ∈ M}
  add_mem' := by simp+contextual [add_mem]
  zero_mem' := by simp
  smul_mem' := by simp+contextual [Submodule.smul_mem]

@[simp] lemma mem_mvPolynomial : x ∈ M.mvPolynomial σ ↔ ∀ i, x.coeff i ∈ M := .rfl

end Module

section Algebra
variable [Algebra R S] {M N : Submodule R S} {x : MvPolynomial σ S} {n : ℕ}

lemma le_mvPolynomial_mul : M.mvPolynomial σ * N.mvPolynomial σ ≤ (M * N).mvPolynomial σ := by
  classical
  rw [mul_le]
  intros x hx y hy k
  rw [MvPolynomial.coeff_mul]
  exact sum_mem fun c hc ↦ mul_mem_mul (hx _) (hy _)

lemma mvPolynomial_pow_le : M.mvPolynomial σ ^ n ≤ (M ^ n).mvPolynomial σ := by
  classical
  induction' n with n IH
  · simpa [MvPolynomial.coeff_one, apply_ite] using ⟨1, map_one _⟩
  · exact (Submodule.mul_le_mul_left IH).trans le_mvPolynomial_mul

end Algebra
end Submodule
