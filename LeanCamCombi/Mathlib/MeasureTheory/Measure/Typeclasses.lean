import Mathlib.MeasureTheory.Measure.Typeclasses

variable {α β : Type*} [MeasurableSpace β] {f g : α → β} {s : Set β}

namespace MeasureTheory
variable [MeasurableSpace α] {μ : Measure α} {s : Set α}

lemma prob_compl_eq_one_sub₀ [IsProbabilityMeasure μ] {s : Set α} (h : NullMeasurableSet s μ) :
    μ sᶜ = 1 - μ s := by rw [measure_compl₀ h (measure_ne_top _ _), measure_univ]

end MeasureTheory
