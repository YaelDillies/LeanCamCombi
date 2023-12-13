import Mathlib.MeasureTheory.Measure.Typeclasses
import LeanCamCombi.Mathlib.MeasureTheory.Measure.MeasureSpace

variable {α β : Type*} [MeasurableSpace β] {f g : α → β} {s : Set β}

namespace MeasureTheory
variable [MeasurableSpace α] {μ : Measure α} {s : Set α}

lemma NullMeasurableSet.prob_compl_eq_one_sub [IsProbabilityMeasure μ] {s : Set α}
    (h : NullMeasurableSet s μ) : μ (sᶜ) = 1 - μ s := by
  rw [h.measure_compl (measure_ne_top _ _), measure_univ]

end MeasureTheory
