import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Additive.ApproximateSubgroup
import Mathlib.Tactic.Bound
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

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

open Fin Finset List
open scoped RightActions

variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G} {k K : ℝ} {m : ℕ}

lemma lemma_2_2 (U V W : Finset G) : #U * #(V⁻¹ * W) ≤ #(U * V) * #(U * W) :=
  Finset.ruzsa_triangle_inequality_invMul_mul_mul ..

lemma lemma_2_3_2 (hA : #(A ^ 2) ≤ K * #A) : #(A⁻¹ * A) ≤ K ^ 2 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
  calc
    (#A * #(A⁻¹ * A) : ℝ) ≤ #(A * A) * #(A * A) := by norm_cast; exact lemma_2_2 ..
    _ ≤ (K * #A) * (K * #A) := by rw [← sq A]; gcongr
    _ = #A * (K ^ 2 * #A) := by ring

-- TODO: fix this @[to_additive]
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
    _ ≤ K ^ 2 * #A := by
      apply lemma_2_3_2 hA
  obtain ⟨F, hFA, hFcard, hASF⟩ : ∃ F ⊆ A, #F ≤ 2 * K ∧ A ⊆ S * F := sorry
  refine ⟨S ^ 2, by gcongr, ?_, ?_, ?_⟩
  · rw [show 2 ^ 12 * K ^ 36 = (2 ^ 4 * K ^ 12) ^ 3 by ring, coe_pow]
    refine .of_small_tripling hS₁ hSsymm ?_
    calc
      (#(S ^ 3) : ℝ)
      _ ≤ #(A * S ^ 3) := mod_cast card_le_card_mul_left hA₀
      _ ≤ #(A * S ^ 3 * A⁻¹) := mod_cast card_le_card_mul_right hA₀.inv
      _ ≤ #(A * S ^ 3 * A⁻¹) := by rfl
      _ ≤ 8 * K ^ 11 * #A := by
        sorry
      _ ≤ 8 * K ^ 11 * #(S * F) := by gcongr
      _ ≤ 8 * K ^ 11 * (#S * #F) := by gcongr; exact mod_cast card_mul_le
      _ ≤ 8 * K ^ 11 * (#S * (2 * K)) := by gcongr
      _ = 2 ^ 4 * K ^ 12 * #S := by ring
  · calc
      (#(S ^ 2) : ℝ)
      _ ≤ #(S * S) := by gcongr; sorry
      _ ≤ #S * #S := mod_cast card_mul_le
      _ ≤ (K ^ 2 * #A) * (K ^ 2 * #A) := by gcongr
      _ ≤ K ^ 4 * #A ^ 2 := by linarith
      _ ≤ K ^ 4 * #(A ^ 2) := sorry
      _ ≤ K ^ 4 * (K * #A) := by gcongr
      _ ≤ K ^ 5 * #A := by linarith
      _ ≤ 1 * K ^ 5 * #A := by linarith
      _ ≤ K * K ^ 5 * #A := by gcongr
      _ ≤ K ^ 1 * K ^ 5 * #A := by linarith
      _ ≤ K ^ 7 * K ^ 5 * #A := by
        gcongr
        · apply hK
        · norm_num
      _ ≤ K ^ 12 * #A := by linarith
      _ ≤ 1 * K ^ 12 * #A := by linarith
      _ ≤ 16 * K ^ 12 * #A := by gcongr; linarith
  · sorry
