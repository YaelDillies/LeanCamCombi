import Mathlib.MeasureTheory.Measure.OpenPos

open scoped Topology ENNReal MeasureTheory

open Set Function Filter

namespace MeasureTheory

namespace Measure

variable {X : Type*} [TopologicalSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

instance IsOpenPosMeasure.to_ae_neBot [Nonempty X] : (ae μ).NeBot :=
  ae_neBot.2 fun h =>
    isOpen_univ.measure_ne_zero μ univ_nonempty <| by rw [h, coe_zero, Pi.zero_apply]

end Measure

end MeasureTheory
