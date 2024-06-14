/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Convex functions are continuous

This file proves that a convex function from a finite dimensional real inner product space to `ℝ` is
continuous.

## TODO

Can this be extended to real normed spaces?
-/

namespace Real
variable {ε r : ℝ}

open Metric

lemma closedBall_eq_segment (hε : 0 ≤ ε) : closedBall r ε = segment ℝ (r - ε) (r + ε) := by
  rw [closedBall_eq_Icc, segment_eq_Icc ((sub_le_self _ hε).trans $ le_add_of_nonneg_right hε)]

end Real

section pi
variable {𝕜 ι : Type*} {E : ι → Type*} [Fintype ι] [LinearOrderedField 𝕜]
  [Π i, AddCommGroup (E i)] [Π i, Module 𝕜 (E i)] {s : Set ι} {t : Π i, Set (E i)} {f : Π i, E i}

lemma mem_convexHull_pi (h : ∀ i ∈ s, f i ∈ convexHull 𝕜 (t i)) : f ∈ convexHull 𝕜 (s.pi t) :=
  sorry -- See `mk_mem_convexHull_prod`

@[simp] lemma convexHull_pi (s : Set ι) (t : Π i, Set (E i)) :
    convexHull 𝕜 (s.pi t) = s.pi (fun i ↦ convexHull 𝕜 (t i)) :=
  Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ ↦ subset_convexHull _ _) $ convex_pi $
    fun _ _ ↦ convex_convexHull _ _) fun _ ↦ mem_convexHull_pi

end pi

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {x : E}

open FiniteDimensional Metric Set
open scoped BigOperators

/-- We can intercalate a polyhedron between an intrinsically open set and one of its elements,
namely a small enough cube. -/
lemma IsOpen.exists_mem_intrinsicInterior_convexHull_finset
  (hs : IsOpen ((↑) ⁻¹' s : Set $ affineSpan ℝ s)) (hx : x ∈ s) :
  ∃ t : Finset E, x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) ∧
    convexHull ℝ (t : Set E) ⊆ s := by
  classical
  lift x to affineSpan ℝ s using subset_affineSpan _ _ hx
  set x : affineSpan ℝ s := x with hx
  clear_value x
  subst hx
  obtain ⟨ε, hε, hεx⟩ := (Metric.nhds_basis_closedBall.1 _).1 (isOpen_iff_mem_nhds.1 hs _ hx)
  set f : Finset (Fin $ finrank ℝ $ vectorSpan ℝ s) → vectorSpan ℝ s :=
    fun u ↦ (ε / ∑ i, ‖finBasis ℝ (vectorSpan ℝ s) i‖) • ∑ i, if i ∈ u then
      finBasis ℝ (vectorSpan ℝ s) i else -finBasis ℝ (vectorSpan ℝ s) i
      with hf
  sorry
  -- set t := Finset.univ.image (fun u, f u +ᵥ x) with ht,
  -- refine ⟨t, _, (convexHull_min _ $ convex_closedBall _ _).trans hεx⟩,
  -- { have hf' : isOpen_map (fun w : fin (finrank ℝ E) → ℝ, x + ∑ i, w i • finBasis ℝ E i) := sorry,
  --   refine interior_maximal _ (hf' _ isOpen_ball) ⟨0, mem_ball_self zero_lt_one,
  --     by simp only [pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]⟩,
  --   rw image_subset_iff,
  --   refine ball_subset_closedBall.trans _,
  --   simp_rw [closedBall_pi _ zero_le_one, Real.closedBall_eq_segment zero_le_one,
  --     ← convexHull_pair, ← convexHull_pi, pi.zero_apply, zero_sub, zero_add, ht, Finset.coe_image,
  --     Finset.coe_univ, image_univ],
  --   refine convexHull_min (fun w hw, subset_convexHull _ _ _) _,
  --   refine ⟨Finset.univ.filter (fun i ↦ w i = 1), _⟩,
  --   sorry,
  --   refine (convex_convexHull _ _).is_linear_preimage _, -- rather need bundled affine preimage
  --   sorry,
  -- },
  -- { have hε' : 0 ≤ ε / finrank ℝ E := by positivity,
  --   simp_rw [ht, Finset.coe_image, Finset.coe_univ,image_univ, range_subset_iff, mem_closedBall,
  --     dist_self_add_left],
  --   rintro u,
  --   have hE : 0 ≤ ∑ i, ‖finBasis ℝ E i‖ := Finset.sum_nonneg (fun x hx, norm_nonneg _),
  --   simp_rw [hf, norm_smul, Real.norm_of_nonneg (div_nonneg hε.le hE), div_mul_comm ε,
  --     mul_le_iff_le_one_left hε],
  --   refine div_le_one_of_le ((norm_sum_le _ _).trans $ Finset.sum_le_sum fun i _, _) hE,
  --   rw [apply_ite norm, norm_neg, if_t_t] }

end

open FiniteDimensional Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {f : E → ℝ}

-- TODO: This proof actually gives local Lipschitz continuity.
-- See `IsOpen.exists_mem_interior_convexHull_finset` for more todo.
protected lemma ConvexOn.continuousOn (hf : ConvexOn ℝ s f) :
  ContinuousOn f (intrinsicInterior ℝ s) := by
  classical
  -- refine isOpen_interior.continuousOn_iff.2 (fun x hx, _),
  -- obtain ⟨t, hxt, hts⟩ := isOpen_interior.exists_mem_interior_convexHull_finset hx,
  -- set M := t.sup' (convexHull_nonempty_iff.1 $ nonempty.mono interior_subset ⟨x, hxt⟩) f,
  -- refine metric.continuous_at_iff.2 (fun ε hε, _),
  -- have : f x ≤ M := le_sup_of_mem_convexHull
  --   (hf.subset (hts.trans interior_subset) $ convex_convexHull _ _) (interior_subset hxt),
  -- refine ⟨ε / (M - f x), _, fun y hy, _⟩,
  -- sorry,
  sorry

protected lemma ConcaveOn.continuousOn (hf : ConcaveOn ℝ s f) :
  ContinuousOn f (intrinsicInterior ℝ s) :=
sorry
