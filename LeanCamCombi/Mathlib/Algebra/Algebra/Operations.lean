import Mathlib.Algebra.Algebra.Operations

open scoped Pointwise

namespace Submodule
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [CommSemiring B] [Algebra R B]
  [IsScalarTower R B B]

instance : IsScalarTower B (Submodule R B) (Submodule R B) := sorry
instance : SMulCommClass B (Submodule R B) (Submodule R B) := sorry

lemma exists_lift_localization {c : A} {f : A →ₐ[R] B} [Invertible (f c)] {s : Set A} {n : ℕ}
    {x : B} (hx : x ∈ span R (⅟(f c) • f.toLinearMap '' s) ^ n) :
    ∃ y ∈ span R s ^ n, f y = x * f c ^ n := by
  rw [span_smul, smul_pow, ← invOf_pow] at hx
  simpa [← map_span, ← Submodule.map_pow, mul_comm, -AlgHom.toLinearMap_apply]
    using smul_mem_pointwise_smul _ (f c ^ n) _ hx

end Submodule
