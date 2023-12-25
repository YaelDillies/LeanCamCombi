import MeasureTheory.Measure.OpenPos

#align_import mathlib.measure_theory.measure.open_pos

open scoped Topology ENNReal MeasureTheory

open Set Function Filter

namespace MeasureTheory

namespace Measure

variable {X : Type _} [TopologicalSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

instance IsOpenPosMeasure.to_ae_neBot [Nonempty X] : μ.ae.ne_bot :=
  ae_neBot.2 fun h =>
    isOpen_univ.measure_ne_zero μ univ_nonempty <| by rw [h, coe_zero, Pi.zero_apply]

end Measure

end MeasureTheory

