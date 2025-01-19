import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import LeanCamCombi.Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# TODO

* Rename `condexp` to `condExp`
* Golf `condexp_const`, no `@`
* Remove useless `haveI`/`letI`
* Make `m` explicit in `condexp_add`, `condexp_sub`, etc...
* See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Conditional.20expectation.20of.20product
  for how to prove that we can pull `m`-measurable continuous linear maps out of the `m`-conditional
  expectation.
-/

open scoped ENNReal

namespace MeasureTheory
variable {Ω R E : Type*} {f : Ω → E}
  {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} {s : Set Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [simp] condexp_const

alias condexp_of_not_integrable := condexp_undef

variable [IsFiniteMeasure μ] [InnerProductSpace ℝ E]

lemma Memℒp.condexpL2_eq_condexp (hm : m ≤ m₀) (hf : Memℒp f 2 μ) :
    (condexpL2 E ℝ hm (hf.toLp _) : Ω → E) =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condexp_of_forall_setIntegral_eq hm
    (memℒp_one_iff_integrable.1 <| hf.mono_exponent one_le_two) ?_ ?_ ?_
  · intros s hs htop
    exact integrableOn_condexpL2_of_measure_ne_top hm htop.ne _
  · intros s hs htop
    rw [integral_condexpL2_eq hm (hf.toLp _) hs htop.ne]
    refine setIntegral_congr_ae (hm _ hs) ?_
    filter_upwards [hf.coeFn_toLp] with ω hω _ using hω
  · exact aeStronglyMeasurable'_condexpL2 hm _

lemma eLpNorm_condexp_le' (hm : m ≤ m₀) (hf : Memℒp f 2 μ) :
    eLpNorm (μ[f | m]) 2 μ ≤ eLpNorm f 2 μ := by
  rw [← eLpNorm_congr_ae (hf.condexpL2_eq_condexp hm)]
  refine le_trans (eLpNorm_condexpL2_le hm _) ?_
  rw [eLpNorm_congr_ae hf.coeFn_toLp]

lemma eLpNorm_condexp_le : eLpNorm (μ[f | m]) 2 μ ≤ eLpNorm f 2 μ := by
  by_cases hm : m ≤ m₀
  swap; simp [condexp_of_not_le hm]
  by_cases hfm : AEStronglyMeasurable f μ
  swap
  rw [condexp_undef (by simp [Integrable, not_and_of_not_left _ hfm])]
  · simp
  by_cases hf : eLpNorm f 2 μ = ∞; simp [hf]
  refine eLpNorm_condexp_le' hm ⟨hfm, Ne.lt_top' fun a ↦ hf (id (Eq.symm a))⟩

protected lemma Memℒp.condexp (hf : Memℒp f 2 μ) : Memℒp (μ[f | m]) 2 μ := by
  by_cases hm : m ≤ m₀
  · exact ⟨(stronglyMeasurable_condexp.mono hm).aestronglyMeasurable,
      eLpNorm_condexp_le.trans_lt hf.eLpNorm_lt_top⟩
  · simp [condexp_of_not_le hm]

section NormedRing
variable [NormedRing R] [NormedSpace ℝ R] [CompleteSpace R] {f g : Ω → R}

lemma condexp_ofNat (n : ℕ) [n.AtLeastTwo] (f : Ω → R) :
    μ[OfNat.ofNat n * f|m] =ᵐ[μ] OfNat.ofNat n * μ[f|m] := by
  simpa [Nat.cast_smul_eq_nsmul] using condexp_smul (μ := μ) (m := m) (n : ℝ) f

end NormedRing

section Real
variable {f : Ω → ℝ}

lemma integral_condexp_sq_le : ∫ ω, (μ[f | m]) ω ^ 2 ∂μ ≤ ∫ ω, f ω ^ 2 ∂μ := sorry

end Real
