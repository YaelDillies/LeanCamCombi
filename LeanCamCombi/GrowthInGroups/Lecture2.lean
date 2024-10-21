
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic
import LeanCamCombi.GrowthInGroups.SmallTripling

open Fin Finset List
open scoped Combinatorics.Additive Pointwise

namespace GrowthInGroups.Lecture2
variable {G : Type*} [DecidableEq G] [CommGroup G] {A : Finset G} {k K : ℝ} {m : ℕ}

-- TODO: Genealise to non-commutative groups
lemma lemma_4_2 (U V W : Finset G) : #U * #(V⁻¹ * W) ≤ #(U * V) * #(U * W) := by
  rw [mul_comm, inv_mul_eq_div, mul_comm _ W, mul_comm #(U * V)]
  exact ruzsa_triangle_inequality_div_mul_mul ..

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

lemma lemma_4_4_1 (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (ε : Fin m → ℤ)
    (hε : ∀ i, |ε i| = 1) :
    #((finRange m).map fun i ↦ A ^ ε i).prod ≤ K ^ (3 * (m - 2)) * #A :=
 small_alternating_pow_of_small_tripling hm hA ε hε

lemma lemma_4_4_2 (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (hAsymm : A⁻¹ = A) :
    #(A ^ m) ≤ K ^ (m - 2) * #A := small_pow_of_small_tripling hm hA hAsymm

end GrowthInGroups.Lecture2
