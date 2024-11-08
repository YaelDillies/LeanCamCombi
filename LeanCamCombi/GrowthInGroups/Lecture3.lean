import LeanCamCombi.Mathlib.Data.Set.Pointwise.Interval
import LeanCamCombi.GrowthInGroups.ApproximateSubgroup

open Fin Finset List
open scoped Pointwise

namespace GrowthInGroups.Lecture3
variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G} {k K : ℝ} {m : ℕ}

lemma lemma_5_1 {A : Finset G} (hA₀ : A.Nonempty) (hAsymm : A⁻¹ = A) (hA : #(A ^ 3) ≤ K * #A) :
    IsApproximateSubgroup (A ^ 2 : Set G) (K ^ 3) := .of_small_tripling hA₀ hAsymm hA

lemma lemma_5_2 {A B : Finset G} (hB : B.Nonempty) (hK : #(A * B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * B / B := ruzsa_covering_mul hB hK

end GrowthInGroups.Lecture3
