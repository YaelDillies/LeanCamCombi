import Mathlib.MeasureTheory.Function.L1Space
import LeanCamCombi.Mathlib.MeasureTheory.Measure.Typeclasses

namespace MeasureTheory
variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β] {c : β}

lemma integrable_const_iff_isFiniteMeasure (hc : c ≠ 0) :
    Integrable (fun _ ↦ c) μ ↔ IsFiniteMeasure μ := by
  simp [integrable_const_iff, hc, isFiniteMeasure_iff]

end MeasureTheory
