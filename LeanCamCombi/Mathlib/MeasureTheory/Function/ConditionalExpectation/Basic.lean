import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# TODO

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
