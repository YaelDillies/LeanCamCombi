import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Additive.ApproximateSubgroup
import Mathlib.Tactic.Bound

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

namespace IsApproximateSubgroup

@[to_additive]
lemma pi {ι : Type*} {G : ι → Type*} [Fintype ι] [∀ i, Group (G i)] {A : ∀ i, Set (G i)} {K : ι → ℝ}
    (hA : ∀ i, IsApproximateSubgroup (K i) (A i)) :
    IsApproximateSubgroup (∏ i, K i) (Set.univ.pi A) where
  one_mem i _ := (hA i).one_mem
  inv_eq_self := by simp [(hA _).inv_eq_self]
  sq_covBySMul := by
    choose F hF hFS using fun i ↦ (hA i).sq_covBySMul
    classical
    refine ⟨Fintype.piFinset F, ?_, ?_⟩
    · calc
        #(Fintype.piFinset F) = ∏ i, (#(F i) : ℝ) := by simp
        _ ≤ ∏ i, K i := by gcongr; exact hF _
    · sorry

end IsApproximateSubgroup

set_option linter.flexible false in
open Finset in
open scoped RightActions in
@[to_additive]
lemma exists_isApproximateSubgroup_of_small_doubling [DecidableEq G] {A : Finset G}
    (hA₀ : A.Nonempty) (hA : #(A ^ 2) ≤ K * #A) :
    ∃ S ⊆ (A⁻¹ * A) ^ 2, IsApproximateSubgroup (2 ^ 12 * K ^ 36) (S : Set G) ∧
      #S ≤ 16 * K ^ 12 * #A ∧ ∃ a ∈ A, #A / (2 * K) ≤ #(A ∩ S <• a) := by
  have hK : 1 ≤ K := one_le_of_le_mul_right₀ (by positivity) <|
    calc (#A : ℝ) ≤ #(A ^ 2) := mod_cast card_le_card_pow two_ne_zero
      _ ≤ K * #A := hA
  let S : Finset G := {g ∈ A⁻¹ * A | #A / (2 * K) ≤ #(A <• g ∩ A)}
  have hS₁ : 1 ∈ S := by simp [S, hA₀.ne_empty]; bound
  have hS₀ : S.Nonempty := ⟨1, hS₁⟩
  have hSA : S ⊆ A⁻¹ * A := filter_subset ..
  have hSsymm : S⁻¹ = S := by ext; simp [S]; sorry
  have hScard := calc
    (#S : ℝ) ≤ #(A⁻¹ * A) := by gcongr
    _ ≤ K ^ 2 * #A := sorry
  obtain ⟨F, hFA, hFcard, hASF⟩ : ∃ F ⊆ A, #F ≤ 2 * K ∧ A ⊆ S * F := sorry
  refine ⟨S ^ 2, by gcongr, ?_, ?_, ?_⟩
  · rw [show 2 ^ 12 * K ^ 36 = (2 ^ 4 * K ^ 12) ^ 3 by ring, coe_pow]
    refine .of_small_tripling hS₁ hSsymm ?_
    calc
      (#(S ^ 3) : ℝ)
      _ ≤ #(A * S ^ 3) := mod_cast card_le_card_mul_left hA₀
      _ ≤ #(A * S ^ 3 * A⁻¹) := mod_cast card_le_card_mul_right hA₀.inv
      _ ≤ 8 * K ^ 11 * #A := sorry
      _ ≤ 8 * K ^ 11 * #(S * F) := by gcongr
      _ ≤ 8 * K ^ 11 * (#S * #F) := by gcongr; exact mod_cast card_mul_le
      _ ≤ 8 * K ^ 11 * (#S * (2 * K)) := by gcongr
      _ = 2 ^ 4 * K ^ 12 * #S := by ring
  · sorry
  · sorry
