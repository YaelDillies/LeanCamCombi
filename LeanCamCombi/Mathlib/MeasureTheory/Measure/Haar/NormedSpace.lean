import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import LeanCamCombi.Mathlib.Analysis.RCLike.Basic

open AddMonoidHom Bornology MeasureTheory MeasureTheory.Measure Metric NNReal Set

open scoped Pointwise Topology

/-- **Cauchy's functional equation**.

A Borel-measurable group hom from a locally compact normed group to `ℝ` or `ℂ` -/
theorem AddMonoidHom.continuous_of_measurable {G K : Type*} [SeminormedAddCommGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [RCLike K] (f : G →+ K)
    (h : Measurable f) : Continuous f :=
  let ⟨_s, hs, hbdd⟩ := f.exists_nhds_isBounded h 0
 f.continuous_of_isBounded_nhds_zero hs hbdd
