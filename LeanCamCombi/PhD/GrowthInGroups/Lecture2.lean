
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic

open Fin Finset List
open scoped Combinatorics.Additive Pointwise

namespace GrowthInGroups.Lecture2
variable {G : Type*} [DecidableEq G] [CommGroup G] {A : Finset G} {k K : ℝ} {m : ℕ}

-- TODO: Genealise to non-commutative groups
lemma lemma_4_2 (U V W : Finset G) : U.card * (V⁻¹ * W).card ≤ (U * V).card * (U * W).card := by
  rw [mul_comm, inv_mul_eq_div, mul_comm _ W, mul_comm (U * V).card]
  exact ruzsa_triangle_inequality_div_mul_mul ..

lemma lemma_4_3_2 (hA : (A ^ 2).card ≤ K * A.card) : (A⁻¹ * A).card ≤ K ^ 2 * A.card := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < A.card)
  calc
    (A.card * (A⁻¹ * A).card : ℝ) ≤ (A * A).card * (A * A).card := by norm_cast; exact lemma_4_2 ..
    _ ≤ (K * A.card) * (K * A.card) := by rw [← sq A]; gcongr
    _ = A.card * (K ^ 2 * A.card) := by ring

lemma lemma_4_3_1 (hA : (A ^ 2).card ≤ K * A.card) : (A * A⁻¹).card ≤ K ^ 2 * A.card := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < A.card)
  calc
    (A.card * (A * A⁻¹).card : ℝ) ≤ (A * A).card * (A * A).card := by
      norm_cast; simpa [← mul_inv_rev] using lemma_4_2 A⁻¹ A⁻¹ A⁻¹
    _ ≤ (K * A.card) * (K * A.card) := by rw [← sq A]; gcongr
    _ = A.card * (K ^ 2 * A.card) := by ring

lemma lemma_4_4_inductive_claim (hm : 3 ≤ m)
    (h : ∀ ε : Fin 3 → ℤ, (∀ i, |ε i| = 1) →
      ((finRange 3).map fun i ↦ A ^ ε i).prod.card ≤ k * A.card)
    (ε : Fin m → ℤ) (hε : ∀ i, |ε i| = 1) :
    ((finRange m).map fun i ↦ A ^ ε i).prod.card ≤ k ^ (m - 2) * A.card := by
  induction' m, hm using Nat.le_induction with m hm ih
  · simpa using h ε hε
  obtain _ | m := m
  · simp at hm
  have hm₀ : m ≠ 0 := by simp at hm; positivity
  have hε₀ i : ε i ≠ 0 := fun h ↦ by simpa [h] using hε i
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp [hε₀]
  have hk : 0 ≤ k :=
    nonneg_of_mul_nonneg_left ((h 1 (by simp)).trans' (by positivity)) (by positivity)
  let π {n} (δ : Fin n → ℤ) : Finset G := ((finRange _).map fun i ↦ A ^ δ i).prod
  let V : Finset G := π ![-ε 1, -ε 0]
  let W : Finset G := π <| tail <| tail ε
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < A.card)
  calc
    (A.card * (π ε).card : ℝ)
      = A.card * (V⁻¹ * W).card := by
      simp [π, V, W, List.finRange_succ_eq_map, Fin.tail, Function.comp_def, mul_assoc]
    _ ≤ (A * V).card * (A * W).card := by norm_cast; exact lemma_4_2 ..
    _ = (π ![1, -ε 1, -ε 0]).card * (π <| cons 1 <| tail <| tail ε).card := by
      simp [π, V, W, List.finRange_succ_eq_map, Fin.tail, Function.comp_def]
    _ ≤ (k * A.card) * (k ^ (m - 1) * A.card) := by
      gcongr
      · exact h ![1, -ε 1, -ε 0] fun i ↦ by fin_cases i <;> simp [hε]
      · exact ih (cons 1 <| tail <| tail ε) <| cons (by simp) (by simp [hε, Fin.tail])
    _ = A.card * (k ^ m * A.card) := by rw [← pow_sub_one_mul hm₀]; ring

lemma lemma_4_4_1_claim_neg_pos_pos (hA : (A ^ 3).card ≤ K * A.card) :
    (A⁻¹ * A ^ 2).card ≤ K ^ 2 * A.card := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < A.card)
  calc
    (A.card * (A⁻¹ * A ^ 2).card : ℝ) ≤ (A * A).card * (A * A ^ 2).card := by
      norm_cast; exact lemma_4_2 A A (A ^ 2)
    _ = (A ^ 2).card * (A ^ 3).card := by simp [pow_succ']
    _ ≤ (K * A.card) * (K * A.card) := by
      gcongr
      calc
        ((A ^ 2).card : ℝ) ≤ (A ^ 3).card := mod_cast hA₀.card_pow_mono (by norm_num)
        _ ≤ K * A.card := hA
    _ = A.card * (K ^ 2 * A.card) := by ring

lemma lemma_4_4_1_claim_neg_neg_pos (hA : (A ^ 3).card ≤ K * A.card) :
    (A⁻¹ ^ 2 * A).card ≤ K ^ 2 * A.card := by
  rw [← card_inv]
  simpa using lemma_4_4_1_claim_neg_pos_pos (A := A) (K := K) (by simpa)

lemma lemma_4_4_1_claim_pos_neg_neg (hA : (A ^ 3).card ≤ K * A.card) :
    (A * A⁻¹ ^ 2).card ≤ K ^ 2 * A.card := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < A.card)
  calc
    (A.card * (A * A⁻¹ ^ 2).card : ℝ) ≤ (A * A).card * (A ^ 2 * A).card := by
      norm_cast
      have := lemma_4_2 A⁻¹ A⁻¹ (A⁻¹ ^ 2)
      simpa only [card_inv, inv_inv, inv_pow, ← mul_inv_rev] using this
    _ = (A ^ 2).card * (A ^ 3).card := by simp [pow_succ]
    _ ≤ (K * A.card) * (K * A.card) := by
      gcongr
      calc
        ((A ^ 2).card : ℝ) ≤ (A ^ 3).card := mod_cast hA₀.card_pow_mono (by norm_num)
        _ ≤ K * A.card := hA
    _ = A.card * (K ^ 2 * A.card) := by ring

lemma lemma_4_4_1_claim_pos_pos_neg (hA : (A ^ 3).card ≤ K * A.card) :
    (A ^ 2 * A⁻¹).card ≤ K ^ 2 * A.card := by
  rw [← card_inv]
  simpa using lemma_4_4_1_claim_pos_neg_neg (A := A) (K := K) (by simpa)

lemma lemma_4_4_1_claim_pos_neg_pos (hA : (A ^ 3).card ≤ K * A.card) :
    (A * A⁻¹ * A).card ≤ K ^ 3 * A.card := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < A.card)
  calc
    (A.card * (A * A⁻¹ * A).card : ℝ) ≤ (A * (A * A⁻¹)).card * (A * A).card := by
      norm_cast; simpa using lemma_4_2 A (A * A⁻¹) A
    _ = (A ^ 2 * A⁻¹).card * (A ^ 2).card := by simp [pow_succ, mul_assoc]
    _ ≤ (K ^ 2 * A.card) * (K * A.card) := by
      gcongr
      · exact lemma_4_4_1_claim_pos_pos_neg hA
      calc
        ((A ^ 2).card : ℝ) ≤ (A ^ 3).card := mod_cast hA₀.card_pow_mono (by norm_num)
        _ ≤ K * A.card := hA
    _ = A.card * (K ^ 3 * A.card) := by ring

lemma lemma_4_4_1_claim_neg_pos_neg (hA : (A ^ 3).card ≤ K * A.card) :
    (A⁻¹ * A * A⁻¹).card ≤ K ^ 3 * A.card := by
  rw [← card_inv]
  simpa [mul_assoc] using lemma_4_4_1_claim_pos_neg_pos (A := A) (K := K) (by simpa)

lemma lemma_4_4_1 (hm : 3 ≤ m) (hA : (A ^ 3).card ≤ K * A.card) (ε : Fin m → ℤ)
    (hε : ∀ i, |ε i| = 1) :
    ((finRange m).map fun i ↦ A ^ ε i).prod.card ≤ K ^ (3 * (m - 2)) * A.card := by
  have hm₀ : m ≠ 0 := by positivity
  have hε₀ i : ε i ≠ 0 := fun h ↦ by simpa [h] using hε i
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp [hm₀, hε₀]
  have hK₁ : 1 ≤ K :=
    one_le_of_le_mul_right₀ (by positivity)
      (hA.trans' <| by norm_cast; exact card_le_card_pow (by norm_num))
  rw [pow_mul]
  refine lemma_4_4_inductive_claim hm (fun δ hδ ↦ ?_) ε hε
  simp only [finRange_succ_eq_map, Nat.reduceAdd, isValue, finRange_zero, map_nil, List.map_cons,
    succ_zero_eq_one, succ_one_eq_two, List.prod_cons, prod_nil, mul_one, ← mul_assoc]
  simp only [zero_le_one, abs_eq, Int.reduceNeg, forall_iff_succ, isValue, succ_zero_eq_one,
    succ_one_eq_two, IsEmpty.forall_iff, and_true] at hδ
  have aux₁₃ : K * A.card ≤ K ^ 3 * A.card :=
    calc
      _ = K ^ 1 * A.card := by simp
      _ ≤ K ^ 3 * A.card := by
        gcongr
        · exact hK₁
        · norm_num
  have aux₂₃ : K ^ 2 * A.card ≤ K ^ 3 * A.card := by
    gcongr
    · exact hK₁
    · norm_num
  obtain ⟨hδ₀ | hδ₀, hδ₁ | hδ₁, hδ₂ | hδ₂⟩ := hδ
  · calc
      _ = ((A ^ 3).card : ℝ) := by simp [*, pow_succ]
      _ ≤ K * A.card := hA
      _ ≤ K ^ 3 * A.card := aux₁₃
  · calc
      _ = ((A ^ 2 * A⁻¹).card : ℝ) := by simp [*, sq]
      _ ≤ K ^ 2 * A.card := lemma_4_4_1_claim_pos_pos_neg hA
      _ ≤ K ^ 3 * A.card := aux₂₃
  · calc
      _ = ((A * A⁻¹ * A).card : ℝ) := by simp [*]
      _ ≤ K ^ 3 * A.card := lemma_4_4_1_claim_pos_neg_pos hA
  · calc
      _ = ((A * A⁻¹ ^ 2).card : ℝ) := by simp [*, sq, mul_assoc]
      _ ≤ K ^ 2 * A.card := lemma_4_4_1_claim_pos_neg_neg hA
      _ ≤ K ^ 3 * A.card := aux₂₃
  · calc
      _ = ((A⁻¹ * A ^ 2).card : ℝ) := by simp [*, sq, mul_assoc]
      _ ≤ K ^ 2 * A.card := lemma_4_4_1_claim_neg_pos_pos hA
      _ ≤ K ^ 3 * A.card := aux₂₃
  · calc
      _ = ((A⁻¹ * A * A⁻¹).card : ℝ) := by simp [*]
      _ ≤ K ^ 3 * A.card := lemma_4_4_1_claim_neg_pos_neg hA
  · calc
      _ = ((A⁻¹ ^ 2 * A).card : ℝ) := by simp [*, sq]
      _ ≤ K ^ 2 * A.card := lemma_4_4_1_claim_neg_neg_pos hA
      _ ≤ K ^ 3 * A.card := aux₂₃
  · calc
      _ = ((A ^ 3).card : ℝ) := by simp [*, pow_succ', ← mul_inv_rev]
      _ ≤ K * A.card := hA
      _ ≤ K ^ 3 * A.card := aux₁₃

lemma lemma_4_4_2 (hm : 3 ≤ m) (hA : (A ^ 3).card ≤ K * A.card) (hAsymm : A⁻¹ = A) :
    (A ^ m).card ≤ K ^ (m - 2) * A.card := by
  have (ε : ℤ) (hε : |ε| = 1) : A ^ ε = A := by
    obtain rfl | rfl := eq_or_eq_neg_of_abs_eq hε <;> simp [hAsymm]
  calc
    ((A ^ m).card : ℝ) = ((finRange m).map fun i ↦ A ^ 1).prod.card := by simp
    _ ≤ K ^ (m - 2) * A.card :=
      lemma_4_4_inductive_claim hm (fun δ hδ ↦ by simpa [this _ (hδ _), pow_succ'] using hA) _
        (by simp)

end GrowthInGroups.Lecture2
