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

def def_4_5 (S : Set G) (K : ℝ) : Prop := IsApproximateSubgroup K S

lemma two_nsmul_Icc_nat (k : ℕ) : (2 • .Icc (-k) k : Set ℤ) = {(-k : ℤ), (k : ℤ)} + .Icc (-k) k := by
  ext x
  rw [two_nsmul]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  . obtain ⟨a, ⟨ha1, ha2⟩, b, ⟨hb1, hb2⟩, rfl⟩ := hx
    obtain hx | hx := Int.lt_or_le (a + b) 0
    . refine ⟨-k, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or], a + b + k,
          ⟨?_, ?_⟩, ?_⟩
      . calc -(k : ℤ) = -k + (-k) + k := by rw [neg_add_cancel_right]
        _ ≤ a + (-k) + k := by simp only [neg_add_cancel_right, ha1]
        _ ≤ a + b + k := by rwa [neg_add_cancel_right, add_assoc, ← sub_le_iff_le_add', add_comm,
              ← sub_le_iff_le_add', sub_self, zero_sub]
      . simp only [add_le_iff_nonpos_left, hx, le_of_lt]
      . simp only [neg_add_cancel_comm_assoc]
    . refine ⟨k, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true], a + b - k,
          ⟨?_, ?_⟩, ?_⟩
      . simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hx]
      . simp only [tsub_le_iff_right, add_le_add ha2 hb2]
      . simp only [add_sub_cancel]
  . obtain ⟨a, ha, b⟩ := hx
    refine ⟨a, ?_, b⟩
    obtain rfl | rfl := ha
    . simp only [Set.mem_Icc, le_refl, neg_le_self_iff, Nat.cast_nonneg, and_self]
    . simp only [Set.mem_Icc, neg_le_self_iff, Nat.cast_nonneg, le_refl, and_self]

lemma two_nsmul_Icc_real : (2 • .Icc (-1) 1 : Set ℝ) = {-1, 1} + .Icc (-1) 1 := by
  ext x
  rw [two_nsmul]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  . obtain ⟨a, ⟨ha1, ha2⟩, b, ⟨hb1, hb2⟩, rfl⟩ := hx
    obtain hx | hx := lt_or_le (a + b) 0
    . refine ⟨-1, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, Set.mem_Icc,
      true_and], a + b + 1, ⟨?_, ?_⟩, ?_⟩
      . calc -1 = -1 + (-1) + 1 := by { exact Eq.symm (neg_add_cancel_comm 1 (-1)) }
              _ ≤ a + (-1) + 1 := by rwa [neg_add_cancel_right, neg_add_cancel_right]
              _ ≤ a + b + 1 := by rwa [neg_add_cancel_right, add_assoc, ← sub_le_iff_le_add',
                                       add_comm, ← sub_le_iff_le_add', sub_self, zero_sub]
      . simp only [add_lt_iff_neg_right, hx, le_of_lt]
      . simp only [neg_add_cancel_comm_assoc]
    . refine ⟨1, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, Set.mem_Icc,
      true_and], a + b - 1, ⟨?_, ?_⟩, ?_⟩
      . simpa only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
      . simp only [tsub_le_iff_right, add_le_add ha2 hb2]
      . simp only [add_sub_cancel]
  . obtain ⟨a, rfl | rfl, b⟩ := hx
    . exact ⟨-1, by simp only [Set.mem_Icc, le_refl, neg_le_self_iff, zero_le_one, and_self,
      true_and], b⟩
    . exact ⟨1, by simp only [Set.mem_Icc, neg_le_self_iff, zero_le_one, le_refl, and_self,
      true_and], b⟩

lemma remark_4_6_1 (k : ℕ) : IsApproximateAddSubgroup 2 (.Icc (-k) k : Set ℤ) where
  zero_mem := by simp
  neg_eq_self := by simp
  two_nsmul_vaddCovered :=
    ⟨{(-k : ℤ), (k : ℤ)}, mod_cast card_le_two, by simp [two_nsmul_Icc_nat]⟩

lemma remark_4_6_2 {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    IsApproximateAddSubgroup (2 ^ Fintype.card ι)
      (Set.univ.pi fun i ↦ .Icc (-k i) (k i) : Set (ι → ℤ)) := by
  simpa using IsApproximateAddSubgroup.pi fun i ↦ remark_4_6_1 (k i)

lemma remark_4_6_3 : IsApproximateAddSubgroup 2 (.Icc (-1) 1 : Set ℝ) where
  zero_mem := by simp
  neg_eq_self := by simp
  two_nsmul_vaddCovered := ⟨{-1, 1}, mod_cast card_le_two, by simp [two_nsmul_Icc_real]⟩

lemma lemma_4_7 {A : Finset G} (hA₁ : 1 ∈ A) (hsymm : A⁻¹ = A) (hA : #(A ^ 3) ≤ K * #A) :
    IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) := .of_small_tripling hA₁ hsymm hA

lemma lemma_4_8 {A B : Finset G} (hB : B.Nonempty) (hK : #(A * B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * B / B := ruzsa_covering_mul hB hK

end GrowthInGroups.Lecture2
