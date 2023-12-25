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

theorem closedBall_eq_segment (hε : 0 ≤ ε) : closedBall r ε = segment ℝ (r - ε) (r + ε) := by
  rw [closed_ball_eq_Icc, segment_eq_Icc ((sub_le_self _ hε).trans <| le_add_of_nonneg_right hε)]

end Real

section Pi

variable {𝕜 ι : Type _} {E : ι → Type _} [Fintype ι] [LinearOrderedField 𝕜]
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] {s : Set ι} {t : ∀ i, Set (E i)} {f : ∀ i, E i}

theorem mem_convexHull_pi (h : ∀ i ∈ s, f i ∈ convexHull 𝕜 (t i)) : f ∈ convexHull 𝕜 (s.pi t) :=
  sorry

-- See `mk_mem_convex_hull_prod`
@[simp]
theorem convexHull_pi (s : Set ι) (t : ∀ i, Set (E i)) :
    convexHull 𝕜 (s.pi t) = s.pi fun i => convexHull 𝕜 (t i) :=
  Set.Subset.antisymm
    (convexHull_min (Set.pi_mono fun i _ => subset_convexHull _ _) <|
      convex_pi fun i _ => convex_convexHull _ _)
    fun f hf => mem_convexHull_pi hf

end Pi

section

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E}
  {x : E}

open FiniteDimensional Metric Set

open scoped BigOperators

/-- We can intercalate a polyhedron between an intrinsically open set and one of its elements,
namely a small enough cube. -/
theorem IsOpen.exists_mem_intrinsicInterior_convexHull_finset
    (hs : IsOpen (coe ⁻¹' s : Set <| affineSpan ℝ s)) (hx : x ∈ s) :
    ∃ t : Finset E,
      x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) ∧ convexHull ℝ (t : Set E) ⊆ s := by
  classical
  lift x to affineSpan ℝ s using subset_affineSpan _ _ hx
  set x : affineSpan ℝ s := x with hx
  clear_value x
  subst hx
  obtain ⟨ε, hε, hεx⟩ := (Metric.nhds_basis_closedBall.1 _).1 (isOpen_iff_mem_nhds.1 hs _ hx)
  set f : Finset (Fin <| finrank ℝ <| vectorSpan ℝ s) → vectorSpan ℝ s := fun u =>
    (ε / ∑ i, ‖fin_basis ℝ (vectorSpan ℝ s) i‖) •
      ∑ i, if i ∈ u then fin_basis ℝ (vectorSpan ℝ s) i else -fin_basis ℝ (vectorSpan ℝ s) i with
    hf
  sorry

-- set t := finset.univ.image (λ u, f u +ᵥ x) with ht,
-- refine ⟨t, _, (convex_hull_min _ $ convex_closed_ball _ _).trans hεx⟩,
-- { have hf' : is_open_map (λ w : fin (finrank ℝ E) → ℝ, x + ∑ i, w i • fin_basis ℝ E i) := sorry,
--   refine interior_maximal _ (hf' _ is_open_ball) ⟨0, mem_ball_self zero_lt_one,
--     by simp only [pi.zero_apply, zero_smul, finset.sum_const_zero, add_zero]⟩,
--   rw image_subset_iff,
--   refine ball_subset_closed_ball.trans _,
--   simp_rw [closed_ball_pi _ zero_le_one, real.closed_ball_eq_segment zero_le_one,
--     ←convex_hull_pair, ←convex_hull_pi, pi.zero_apply, zero_sub, zero_add, ht, finset.coe_image,
--     finset.coe_univ, image_univ],
--   refine convex_hull_min (λ w hw, subset_convex_hull _ _ _) _,
--   refine ⟨finset.univ.filter (λ i, w i = 1), _⟩,
--   sorry,
--   refine (convex_convex_hull _ _).is_linear_preimage _, -- rather need bundled affine preimage
--   sorry,
-- },
-- { have hε' : 0 ≤ ε / finrank ℝ E := by positivity,
--   simp_rw [ht, finset.coe_image, finset.coe_univ,image_univ, range_subset_iff, mem_closed_ball,
--     dist_self_add_left],
--   rintro u,
--   have hE : 0 ≤ ∑ i, ‖fin_basis ℝ E i‖ := finset.sum_nonneg (λ x hx, norm_nonneg _),
--   simp_rw [hf, norm_smul, real.norm_of_nonneg (div_nonneg hε.le hE), div_mul_comm ε,
--     mul_le_iff_le_one_left hε],
--   refine div_le_one_of_le ((norm_sum_le _ _).trans $ finset.sum_le_sum $ λ i _, _) hE,
--   rw [apply_ite norm, norm_neg, if_t_t] }
end

open FiniteDimensional Metric Set

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E}
  {f : E → ℝ}

-- TODO: This proof actually gives local Lipschitz continuity.
-- See `is_open.exists_mem_interior_convex_hull_finset` for more todo.
protected theorem ConvexOn.continuousOn (hf : ConvexOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) := by
  classical-- refine is_open_interior.continuous_on_iff.2 (λ x hx, _),
  -- obtain ⟨t, hxt, hts⟩ := is_open_interior.exists_mem_interior_convex_hull_finset hx,
  -- set M := t.sup' (convex_hull_nonempty_iff.1 $ nonempty.mono interior_subset ⟨x, hxt⟩) f,
  -- refine metric.continuous_at_iff.2 (λ ε hε, _),
  -- have : f x ≤ M := le_sup_of_mem_convex_hull
  --   (hf.subset (hts.trans interior_subset) $ convex_convex_hull _ _) (interior_subset hxt),
  -- refine ⟨ε / (M - f x), _, λ y hy, _⟩,
  -- sorry,
  sorry

protected theorem ConcaveOn.continuousOn (hf : ConcaveOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) :=
  sorry
