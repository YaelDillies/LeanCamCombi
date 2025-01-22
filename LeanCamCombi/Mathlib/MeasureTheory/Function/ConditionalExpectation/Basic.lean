import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# TODO

* Golf `condExp_const`, no `@`
* Remove useless `haveI`/`letI`
* Make `m` explicit in `condExp_add`, `condExp_sub`, etc...
* See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Conditional.20expectation.20of.20product
  for how to prove that we can pull `m`-measurable continuous linear maps out of the `m`-conditional
  expectation.
-/

open scoped ENNReal

namespace MeasureTheory
variable {Ω R E : Type*} {f : Ω → E}
  {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} {s : Set Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [simp] condExp_const

alias condExp_of_not_integrable := condExp_undef

section NormedRing
variable [NormedRing R] [NormedSpace ℝ R] [CompleteSpace R] {f g : Ω → R}

lemma condExp_ofNat (n : ℕ) [n.AtLeastTwo] (f : Ω → R) :
    μ[OfNat.ofNat n * f|m] =ᵐ[μ] OfNat.ofNat n * μ[f|m] := by
  simpa [Nat.cast_smul_eq_nsmul] using condExp_smul (μ := μ) (m := m) (n : ℝ) f

end NormedRing

variable [IsFiniteMeasure μ] [InnerProductSpace ℝ E]

lemma Memℒp.condExpL2_ae_eq_condExp (hm : m ≤ m₀) (hf : Memℒp f 2 μ) :
    condExpL2 E ℝ hm hf.toLp =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm
    (memℒp_one_iff_integrable.1 <| hf.mono_exponent one_le_two)
    (fun s hs htop ↦ integrableOn_condExpL2_of_measure_ne_top hm htop.ne _) (fun s hs htop ↦ ?_)
    (aeStronglyMeasurable'_condExpL2 hm _)
  rw [integral_condExpL2_eq hm (hf.toLp _) hs htop.ne]
  refine setIntegral_congr_ae (hm _ hs) ?_
  filter_upwards [hf.coeFn_toLp] with ω hω _ using hω

lemma eLpNorm_condExp_le : eLpNorm (μ[f | m]) 2 μ ≤ eLpNorm f 2 μ := by
  by_cases hm : m ≤ m₀; swap
  · simp [condExp_of_not_le hm]
  by_cases hfm : AEStronglyMeasurable f μ; swap
  · rw [condExp_undef (by simp [Integrable, not_and_of_not_left _ hfm])]
    simp
  obtain hf | hf := eq_or_ne (eLpNorm f 2 μ) ∞
  · simp [hf]
  replace hf : Memℒp f 2 μ := ⟨hfm, Ne.lt_top' fun a ↦ hf (id (Eq.symm a))⟩
  rw [← eLpNorm_congr_ae (hf.condExpL2_ae_eq_condExp hm)]
  refine le_trans (eLpNorm_condExpL2_le hm _) ?_
  rw [eLpNorm_congr_ae hf.coeFn_toLp]

protected lemma Memℒp.condExp (hf : Memℒp f 2 μ) : Memℒp (μ[f | m]) 2 μ := by
  by_cases hm : m ≤ m₀
  · exact ⟨(stronglyMeasurable_condExp.mono hm).aestronglyMeasurable,
      eLpNorm_condExp_le.trans_lt hf.eLpNorm_lt_top⟩
  · simp [condExp_of_not_le hm]
