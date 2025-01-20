import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

open Filter

namespace MeasureTheory
variable {α β γ : Type*}
  {m₀ m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] [TopologicalSpace γ]

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
lemma _root_.Continuous.comp_aestronglyMeasurable' {g : β → γ} {f : α → β} (hg : Continuous g)
    (hf : AEStronglyMeasurable' m₀ f μ) : AEStronglyMeasurable' m₀ (fun x => g (f x)) μ :=
  ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩
