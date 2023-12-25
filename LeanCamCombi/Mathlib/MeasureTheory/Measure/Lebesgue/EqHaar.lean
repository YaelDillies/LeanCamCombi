import MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.OpenPos

#align_import mathlib.measure_theory.measure.lebesgue.eq_haar

open TopologicalSpace Set Filter Metric

open scoped ENNReal Pointwise Topology NNReal

namespace MeasureTheory

namespace Measure

/-! ### Normed groups -/


section SeminormedGroup

variable {G : Type _} [MeasurableSpace G] [Group G] [TopologicalSpace G] [T2Space G]
  [TopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] [LocallyCompactSpace G]

variable {H : Type _} [MeasurableSpace H] [SeminormedGroup H] [OpensMeasurableSpace H]

open Metric

@[to_additive]
theorem Measurable.exists_nhds_one_isBounded (f : G →* H) (h : Measurable f)
    (μ : Measure G := by exact MeasureTheory.MeasureSpace.volume) [μ.IsHaarMeasure] :
    ∃ s, s ∈ 𝓝 (1 : G) ∧ IsBounded (f '' s) :=
  by
  obtain ⟨r, hr⟩ := exists_pos_preimage_ball f (1 : H) (NeZero.ne μ)
  refine' ⟨_, div_mem_nhds_one_of_haar_pos μ (f ⁻¹' ball 1 r) (h measurableSet_ball) hr, _⟩
  rw [image_div]
  exact
    (bounded_ball.mono <| image_preimage_subset _ _).div
      (bounded_ball.mono <| image_preimage_subset _ _)

end SeminormedGroup

end Measure

end MeasureTheory

