import Mathlib.Algebra.Algebra.Operations

namespace Submodule

@[simp]
lemma one_le_iff {R S} [CommSemiring R] [Semiring S] [Module R S] {M : Submodule R S} :
    1 ≤ M ↔ 1 ∈ M := by
  rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]

lemma restrictScalars_pow {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] [SMul A B] [Module A C] [Module B C]
    [IsScalarTower A C C] [IsScalarTower B C C] [IsScalarTower A B C]
    {I : Submodule B C} :
    ∀ {n : ℕ}, (hn : n ≠ 0) → (I ^ n).restrictScalars A = I.restrictScalars A ^ n
  | 1, _ => by simp [Submodule.pow_one]
  | n + 2, _ => by
    simp [Submodule.pow_succ (n := n + 1), restrictScalars_mul, restrictScalars_pow n.succ_ne_zero]

end Submodule
