/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

#align_import mathlib.analysis.cauchy_equation

/-!
# Cauchy's Functional Equation

This file contains the classical results about the Cauchy's functional equation
`f (x + y) = f x + f y` for functions `f : ℝ → ℝ`. In this file, we prove that the solutions to this
equation are linear up to the case when `f` is a Lebesgue measurable functions, while also deducing
intermediate well-known variants.
-/


open AddMonoidHom MeasureTheory MeasureTheory.Measure Metric NNReal Set

open scoped Pointwise Topology

section SeminormedGroup

open TopologicalSpace

variable {G H : Type _} [SeminormedAddGroup G] [TopologicalAddGroup G] [IsROrC H] {s : Set G}

theorem AddMonoidHom.continuous_of_isBounded_nhds_zero (f : G →+ H) (hs : s ∈ 𝓝 (0 : G))
    (hbounded : Bounded (f '' s)) : Continuous f :=
  by
  obtain ⟨δ, hδ, hUε⟩ := metric.mem_nhds_iff.mp hs
  obtain ⟨C, hC⟩ := (bounded_iff_subset_ball 0).1 (hbounded.mono <| image_subset f hUε)
  refine' continuous_of_continuousAt_zero _ (continuous_at_iff.2 fun ε (hε : _ < _) => _)
  simp only [gt_iff_lt, dist_zero_right, _root_.map_zero, exists_prop]
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  obtain hC₀ | hC₀ := le_or_lt C 0
  · refine' ⟨δ, hδ, fun x hxδ => _⟩
    rwa [eq_of_dist_eq_zero
        (dist_nonneg.antisymm' <|
          (mem_closed_ball.1 <| hC <| mem_image_of_mem f <| mem_ball_zero_iff.2 hxδ).trans hC₀),
      norm_zero]
  have hnpos : 0 < (n : ℝ) := (div_pos hC₀ hε).trans hn
  refine' ⟨δ / n, div_pos hδ hnpos, fun x hxδ => _⟩
  have h2 : f (n • x) = n • f x := map_nsmul f _ _
  have hn' : (n : H) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simpa using hnpos)
  simp_rw [nsmul_eq_mul, mul_comm (n : H), ← div_eq_iff hn'] at h2 
  replace hxδ : ‖n • x‖ < δ
  · refine' (norm_nsmul_le' _ _).trans_lt _
    simpa only [norm_mul, Real.norm_coe_nat, lt_div_iff hnpos, mul_comm] using hxδ
  rw [← h2, norm_div, IsROrC.norm_natCast, div_lt_iff' hnpos, ← mem_ball_zero_iff]
  rw [div_lt_iff hε] at hn 
  exact hC.trans (closed_ball_subset_ball hn) (mem_image_of_mem _ <| mem_ball_zero_iff.2 hxδ)

end SeminormedGroup

variable {ι : Type _} [Fintype ι] {s : Set ℝ} {a : ℝ}

local notation "ℝⁿ" => ι → ℝ

theorem AddMonoidHom.measurable_of_continuous (f : ℝ →+ ℝ) (h : Measurable f) : Continuous f :=
  let ⟨s, hs, hbdd⟩ := h.exists_nhds_zero_bounded f
  f.continuous_of_isBounded_nhds_zero hs hbdd

-- do we want this one and where would it go?
theorem isLinearMap_iff_apply_eq_apply_one_hMul {M : Type _} [CommSemiring M] (f : M →+ M) :
    IsLinearMap M f ↔ ∀ x : M, f x = f 1 * x :=
  by
  refine' ⟨fun h x => _, fun h => ⟨map_add f, fun c x => _⟩⟩
  · convert h.2 x 1 using 1
    · simp only [Algebra.id.smul_eq_mul, mul_one]
    · simp only [mul_comm, Algebra.id.smul_eq_mul]
  · rw [smul_eq_mul, smul_eq_mul, h (c * x), h x, ← mul_assoc, mul_comm _ c, mul_assoc]

theorem is_linear_rat (f : ℝ →+ ℝ) (q : ℚ) : f q = f 1 * q :=
  by
  have := map_rat_cast_smul f ℚ ℚ q (1 : ℝ)
  simpa [mul_comm] using this

theorem additive_isBounded_of_isBounded_on_interval (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a)
    (h : Bounded (f '' s)) : ∃ V, V ∈ 𝓝 (0 : ℝ) ∧ Bounded (f '' V) :=
  by
  rcases metric.mem_nhds_iff.mp hs with ⟨δ, hδ, hδa⟩
  refine' ⟨ball 0 δ, ball_mem_nhds 0 hδ, _⟩
  rw [isBounded_iff_forall_norm_le]
  simp only [mem_image, mem_ball_zero_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 h
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hM 
  refine'
    ⟨M + M, fun x hxδ => (norm_le_add_norm_add _ <| f a).trans <| add_le_add _ <| hM _ <| hδa _⟩
  · rw [← map_add f]
    refine' hM _ (hδa _)
    simp only [mem_ball]
    convert hxδ
    rw [← dist_zero_right, ← dist_add_right x 0 a, zero_add]
  · simpa [mem_ball, dist_self]

-- to generalize
theorem AddMonoidHom.continuousAt_iff_continuousAt_zero (f : ℝ →+ ℝ) :
    ContinuousAt f a ↔ ContinuousAt f 0 :=
  by
  refine'
    ⟨fun ha =>
      continuous_at_iff.2 fun ε hε => Exists₂.imp (fun δ hδ => _) (continuous_at_iff.1 ha ε hε),
      fun h => (continuous_of_continuousAt_zero f h).ContinuousAt⟩
  refine' fun hδf y hyδ => _
  replace hyδ : dist (y + a) a < δ
  · convert hyδ using 1
    simp only [dist_eq_norm, sub_zero, add_sub_cancel]
  convert hδf hyδ using 1
  simp only [dist_eq_norm, map_sub, _root_.map_add, _root_.map_zero, sub_zero, add_sub_cancel]

theorem Continuous.is_linear_real (f : ℝ →+ ℝ) (h : Continuous f) : IsLinearMap ℝ f :=
  (f.toRealLinearMap h).toLinearMap.isLinear

theorem isLinearMap_real_of_isBounded_nhds (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a) (hf : Bounded (f '' s)) :
    IsLinearMap ℝ f :=
  let ⟨V, hV0, hVb⟩ := additive_isBounded_of_isBounded_on_interval f hs hf
  (f.continuous_of_isBounded_nhds_zero hV0 hVb).is_linear_real f

theorem MonotoneOn.isLinearMap_real (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a) (hf : MonotoneOn f s) :
    IsLinearMap ℝ f := by
  obtain ⟨t, ht, h⟩ := metric.mem_nhds_iff.mp hs
  refine' isLinearMap_real_of_isBounded_nhds f (closed_ball_mem_nhds a <| half_pos ht) _
  replace h := (closed_ball_subset_ball <| half_lt_self ht).trans h
  rw [Real.closedBall_eq_Icc] at h ⊢
  have ha : a - t / 2 ≤ a + t / 2 := by linarith
  refine' bounded_of_bdd_above_of_bdd_below (hf.map_bdd_above h _) (hf.map_bdd_below h _)
  · refine' ⟨a + t / 2, _, h <| right_mem_Icc.2 ha⟩
    rw [upperBounds_Icc ha]
    exact left_mem_Ici
  · refine' ⟨a - t / 2, _, h <| left_mem_Icc.2 ha⟩
    rw [lowerBounds_Icc ha]
    exact right_mem_Iic

