import Mathlib.Analysis.Matrix
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import LeanCamCombi.GrowthInGroups.ApproximateSubgroup

open Group
open scoped Finset MatrixGroups Pointwise

namespace GrowthInGroups.Lecture3
variable {n : Type*} [Fintype n] [DecidableEq n] {K C₀ C : ℝ}

attribute [instance] Matrix.linftyOpNormedRing

lemma fact_6_1 (S T : GL n ℂ) :
    ‖(S * T * S⁻¹ * T⁻¹ - 1 : Matrix n n ℂ)‖ ≤
      2 * ‖(S⁻¹ : Matrix n n ℂ)‖ * ‖(T⁻¹ : Matrix n n ℂ)‖ *
        ‖(S - 1 : Matrix n n ℂ)‖ * ‖(T - 1 : Matrix n n ℂ)‖ := by
  simpa using norm_commutator_units_sub_one_le S T

open scoped Classical in
lemma lemma_6_2 (hC₀ : Fintype.card n < C₀) (K : ℝ) :
    ∃ δ : ℝ,
      ∀ (A : Finset (GL n ℂ)) (hA : IsApproximateSubgroup K A.toSet) (hC₀ : ∀ a ∈ A, ‖a.val‖ ≤ C₀),
        ∃ γ ∈ A ^ 2, δ * #A ≤ #{x ∈ A ^ 4 | Commute γ x} := sorry

lemma corollary_6_3 (K C₀ : ℝ) :
    ∃ C > 0, ∀ (A : Set SL(2, ℂ)) (hA : IsApproximateSubgroup K A),
      ∃ (Z : Subgroup SL(2, ℂ)) (hH : ∀ x ∈ Z, ∀ y ∈ Z, Commute x y) (F : Finset SL(2, ℂ)),
        #F ≤ C ∧ A ⊆ F * Z := sorry

/-- The **Breuillard-Green-Tao theorem**. -/
theorem theorem_6_4 (hK : 0 ≤ K) :
    ∃ C > 0, ∀ {G} [Group G] [DecidableEq G] (A : Set G) (hA : IsApproximateSubgroup K A),
      ∃ (H : Subgroup G) (N : Subgroup H) (hD : N.Normal) (F : Finset G),
        upperCentralSeries (H ⧸ N) C = ⊤ ∧ ((↑) '' (N : Set H) : Set G) ⊆ (A / A) ^ 4 ∧
          A ⊆ F * H := sorry

lemma theorem_6_5 {G : Type*} [Group G] [DecidableEq G] {S : Finset G} (hSsymm : S⁻¹ = S)
    (hSgen : (Subgroup.closure (S : Set G) : Set G) = .univ) {d : ℕ}
    (hS : ∀ n : ℕ, #(S ^ n) ≤ C * n ^ d) : IsVirtuallyNilpotent G := sorry

end GrowthInGroups.Lecture3
