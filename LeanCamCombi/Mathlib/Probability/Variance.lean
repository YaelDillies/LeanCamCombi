import Mathlib.Probability.Variance

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω} {s : Set Ω}

scoped notation "Var[" X " ; " μ "]" => ProbabilityTheory.variance X μ

lemma variance_eq_integral (hX : AEMeasurable (fun ω ↦ (‖X ω - ∫ ω', X ω' ∂μ‖₊ : ℝ≥0∞) ^ 2) μ) :
    Var[X ; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ := by
  simp [variance, evariance, ← integral_toReal hX (by simp [← ENNReal.coe_pow])]
