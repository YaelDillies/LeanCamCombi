import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open TopologicalSpace Set Filter Metric MeasureTheory Measure

open scoped ENNReal Pointwise Topology NNReal


/-! ### Normed groups -/


section SeminormedGroup

variable {G : Type*} [MeasurableSpace G] [Group G] [TopologicalSpace G]
  [TopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G]

variable {H : Type*} [MeasurableSpace H] [SeminormedGroup H] [OpensMeasurableSpace H]

open Metric Bornology

@[to_additive]
theorem Measurable.exists_nhds_one_isBounded (f : G →* H) (h : Measurable f)
    (μ : Measure G := by exact MeasureTheory.MeasureSpace.volume) [μ.IsHaarMeasure]
    [InnerRegular μ] :
    ∃ s, s ∈ 𝓝 (1 : G) ∧ IsBounded (f '' s) := by
  obtain ⟨r, hr⟩ := exists_pos_preimage_ball f (1 : H) (NeZero.ne μ)
  refine ⟨_, div_mem_nhds_one_of_haar_pos μ (f ⁻¹' ball 1 r) (h measurableSet_ball) hr, ?_⟩
  rw [image_div]
  exact (isBounded_ball.subset <| image_preimage_subset _ _).div
    (isBounded_ball.subset <| image_preimage_subset _ _)

end SeminormedGroup
