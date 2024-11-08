import LeanCamCombi.Mathlib.Data.Set.Pointwise.Interval
import LeanCamCombi.GrowthInGroups.ApproximateSubgroup

open Fin Finset List
open scoped Pointwise

namespace GrowthInGroups.Lecture3
variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G} {k K : ℝ} {m : ℕ}

lemma lemma_5_1 {A : Finset G} (hA₀ : A.Nonempty) (hsymm : A⁻¹ = A) (hA : #(A ^ 3) ≤ K * #A) :
    IsApproximateSubgroup (A ^ 2 : Set G) (K ^ 2) := .of_small_tripling hA₀ hsymm hA

-- TODO: Generalise Ruzsa covering to non-abelian groups
lemma lemma_5_2 {A B : Finset G} (hK : #(A * B) ≤ K * #B) : ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * (B / B) := by
  sorry
  -- obtain ⟨F, hF⟩ := Finset.exists_subset_mul_div A _

end GrowthInGroups.Lecture3
