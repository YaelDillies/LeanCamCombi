import Mathlib.Algebra.Algebra.Operations

namespace Submodule

@[simp]
lemma one_le_iff {R S} [CommSemiring R] [Semiring S] [Module R S] {M : Submodule R S} :
    1 ≤ M ↔ 1 ∈ M := by
  rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]

lemma restrictScalars_pow {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] [SMul A B] [Module A C] [Module B C]
    [IsScalarTower A C C] [IsScalarTower B C C] [IsScalarTower A B C]
    {I : Submodule B C} {n : ℕ} (hn : n ≠ 0) :
    (I ^ n).restrictScalars A = I.restrictScalars A ^ n := by
  cases' n with n
  · contradiction
  induction n with
  | zero =>
    simp [Submodule.pow_one]
  | succ n IH =>
    simp only [Submodule.pow_succ (n := n + 1), Submodule.restrictScalars_mul, IH (by simp)]

end Submodule
