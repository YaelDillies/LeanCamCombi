import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace MeasureTheory
variable {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α}

/-- Pull-out property of the conditional expectation. -/
lemma condexp_mul_stronglyMeasurable {f g : α → ℝ} (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g := by
  simpa [mul_comm] using condexp_stronglyMeasurable_mul hg (mul_comm f g ▸ hfg) hf
