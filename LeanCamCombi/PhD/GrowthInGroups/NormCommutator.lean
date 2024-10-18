import Mathlib.Analysis.RCLike.Basic
import LeanCamCombi.Mathlib.Analysis.Normed.Field.Basic

variable {𝕜 : Type*} [NormedRing 𝕜] {a b : 𝕜ˣ}

lemma norm_commutator_sub_one_le :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ ≤ 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ :=
  calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a : 𝕜) * a⁻¹.val * b⁻¹.val‖ := by
      simp [sub_mul, *]
    _ ≤ ‖(a * b - b * a : 𝕜)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le'
    _ = ‖(a - 1 : 𝕜) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ ≤ (‖(a - 1 : 𝕜) * (b - 1)‖ + ‖(b - 1 : 𝕜) * (a - 1)‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr; exact norm_sub_le ..
    _ ≤ (‖a.val - 1‖ * ‖b.val - 1‖ + ‖b.val - 1‖ * ‖a.val - 1‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr <;> exact norm_mul_le ..
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring
