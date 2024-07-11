import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.NormedSpace.AddTorsorBases

open AffineBasis FiniteDimensional Metric Set
open scoped Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {x : E}

/-- We can intercalate a polyhedron between a point and one of its neighborhoods. -/
lemma exists_mem_interior_convexHull_finset (hs : s ∈ 𝓝 x) :
    ∃ t : Finset E, x ∈ interior (convexHull ℝ t : Set E) ∧ convexHull ℝ t ⊆ s := by
  classical
  wlog hx : x = 0
  · obtain ⟨t, ht⟩ := this (s := -x +ᵥ s) (by simpa using vadd_mem_nhds (-x) hs) rfl
    use x +ᵥ t
    simpa [subset_set_vadd_iff, mem_vadd_set_iff_neg_vadd_mem, convexHull_vadd, interior_vadd]
      using ht
  subst hx
  obtain ⟨b⟩ := exists_affineBasis_of_finiteDimensional
    (ι := Fin (finrank ℝ E + 1)) (k := ℝ) (P := E) (by simp)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  set u : Finset E := -Finset.univ.centroid ℝ b +ᵥ Finset.univ.image b
  have hu₀ : 0 ∈ interior (convexHull ℝ u : Set E) := by
    simpa [u, convexHull_vadd, interior_vadd, mem_vadd_set_iff_neg_vadd_mem]
      using b.centroid_mem_interior_convexHull
  have hu : u.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h ↦ by simp [h] at hu₀
  have hunorm : (u : Set E) ⊆ closedBall 0 (u.sup' hu (‖·‖) + 1) := by
    simp only [subset_def, Finset.mem_coe, mem_closedBall, dist_zero_right, ← sub_le_iff_le_add,
      Finset.le_sup'_iff]
    exact fun x hx ↦ ⟨x, hx, by simp⟩
  set ε' : ℝ := ε / 2 / (u.sup' hu (‖·‖) + 1)
  have hε' : 0 < ε' := by
    dsimp [ε']
    obtain ⟨x, hx⟩ := id hu
    have : 0 ≤ u.sup' hu (‖·‖) := Finset.le_sup'_of_le _ hx (norm_nonneg _)
    positivity
  set t : Finset E := ε' • u
  have hε₀ : 0 < ε / 2 := by positivity
  have htnorm : (t : Set E) ⊆ closedBall 0 (ε / 2) := by
    simp [t, Set.set_smul_subset_iff₀ hε'.ne', hε₀.le, _root_.smul_closedBall, abs_of_nonneg hε'.le]
    simpa [ε',  hε₀.ne'] using hunorm
  refine ⟨t, ?_, ?_⟩
  · simpa [t, interior_smul₀, convexHull_smul, zero_mem_smul_set_iff, hε'.ne']
  calc
    convexHull ℝ t ⊆ closedBall 0 (ε / 2) := convexHull_min htnorm (convex_closedBall ..)
    _ ⊆ ball 0 ε := closedBall_subset_ball (by linarith)
    _ ⊆ s := hεs
