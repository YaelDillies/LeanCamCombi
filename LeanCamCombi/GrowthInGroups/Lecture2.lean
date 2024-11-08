import LeanCamCombi.Mathlib.Data.Set.Pointwise.Interval
import LeanCamCombi.GrowthInGroups.ApproximateSubgroup

open Fin Finset List
open scoped Pointwise

namespace GrowthInGroups.Lecture2
variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G} {k K : ℝ} {m : ℕ}

lemma lemma_4_2 (U V W : Finset G) : #U * #(V⁻¹ * W) ≤ #(U * V) * #(U * W) := by
  exact ruzsa_triangle_inequality_invMul_mul_mul ..

lemma lemma_4_3_2 (hA : #(A ^ 2) ≤ K * #A) : #(A⁻¹ * A) ≤ K ^ 2 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
  calc
    (#A * #(A⁻¹ * A) : ℝ) ≤ #(A * A) * #(A * A) := by norm_cast; exact lemma_4_2 ..
    _ ≤ (K * #A) * (K * #A) := by rw [← sq A]; gcongr
    _ = #A * (K ^ 2 * #A) := by ring

lemma lemma_4_3_1 (hA : #(A ^ 2) ≤ K * #A) : #(A * A⁻¹) ≤ K ^ 2 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
  calc
    (#A * #(A * A⁻¹) : ℝ) ≤ #(A * A) * #(A * A) := by
      norm_cast; simpa [← mul_inv_rev] using lemma_4_2 A⁻¹ A⁻¹ A⁻¹
    _ ≤ (K * #A) * (K * #A) := by rw [← sq A]; gcongr
    _ = #A * (K ^ 2 * #A) := by ring

lemma lemma_4_4_1 (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (ε : Fin m → ℤ) (hε : ∀ i, |ε i| = 1) :
    #((finRange m).map fun i ↦ A ^ ε i).prod ≤ K ^ (3 * (m - 2)) * #A :=
 small_alternating_pow_of_small_tripling' hm hA ε hε

lemma lemma_4_4_2 (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (hAsymm : A⁻¹ = A) :
    #(A ^ m) ≤ K ^ (m - 2) * #A := small_pow_of_small_tripling' hm hA hAsymm

def def_4_5 (S : Set G) (K : ℝ) : Prop := IsApproximateSubgroup S K

lemma two_nsmul_Icc_nat (k : ℕ) : (2 • .Icc (-k) k : Set ℤ) = {(-k : ℤ), (k : ℤ)} + .Icc (-k) k :=
  sorry

lemma two_nsmul_Icc_real : (2 • .Icc (-1) 1 : Set ℝ) = {-1, 1} + .Icc (-1) 1 := sorry

lemma remark_4_6_1 (k : ℕ) : IsApproximateAddSubgroup (.Icc (-k) k : Set ℤ) 2 where
  nonempty := ⟨0, by simp⟩
  neg_eq_self := by simp
  exists_two_nsmul_subset_add :=
    ⟨{(-k : ℤ), (k : ℤ)}, mod_cast card_le_two, by simp [two_nsmul_Icc_nat]⟩

lemma remark_4_6_2 {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    IsApproximateAddSubgroup (Set.univ.pi fun i ↦ .Icc (-k i) (k i) : Set (ι → ℤ))
      (2 ^ Fintype.card ι) := by
  simpa using IsApproximateAddSubgroup.pi fun i ↦ remark_4_6_1 (k i)

lemma remark_4_6_3 : IsApproximateAddSubgroup (.Icc (-1) 1 : Set ℝ) 2 where
  nonempty := ⟨0, by simp⟩
  neg_eq_self := by simp
  exists_two_nsmul_subset_add := ⟨{-1, 1}, mod_cast card_le_two, by simp [two_nsmul_Icc_real]⟩

lemma lemma_4_7 {A : Finset G} (hA₀ : A.Nonempty) (hsymm : A⁻¹ = A) (hA : #(A ^ 3) ≤ K * #A) :
    IsApproximateSubgroup (A ^ 2 : Set G) (K ^ 3) := .of_small_tripling hA₀ hsymm hA

lemma lemma_4_8 {A B : Finset G} (hB : B.Nonempty) (hK : #(A * B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * B / B := ruzsa_covering_mul hB hK

end GrowthInGroups.Lecture2
