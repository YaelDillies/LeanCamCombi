/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import Mathlib.Topology.Instances.RealVectorSpace
import LeanCamCombi.Mathlib.Analysis.RCLike.Basic

/-!
# Cauchy's Functional Equation

This file contains the classical results about the Cauchy's functional equation
`f (x + y) = f x + f y` for functions `f : ℝ → ℝ`. In this file, we prove that the solutions to this
equation are linear up to the case when `f` is a Lebesgue measurable functions, while also deducing
intermediate well-known variants.
-/

open AddMonoidHom Bornology Metric NNReal Set

open scoped Pointwise Topology

variable {ι : Type*} [Fintype ι] {s : Set ℝ} {a : ℝ}

local notation "ℝⁿ" => ι → ℝ

-- do we want this one and where would it go?
theorem isLinearMap_iff_apply_eq_apply_one_mul {M : Type} [CommSemiring M] (f : M →+ M) :
    IsLinearMap M f ↔ ∀ x : M, f x = f 1 * x := by
  refine ⟨fun h x => ?_, fun h => ⟨map_add f, fun c x => ?_⟩⟩
  · convert h.2 x 1 using 1
    · simp only [Algebra.id.smul_eq_mul, mul_one]
    · simp only [mul_comm, Algebra.id.smul_eq_mul]
  · rw [smul_eq_mul, smul_eq_mul, h (c * x), h x, ← mul_assoc, mul_comm _ c, mul_assoc]

theorem is_linear_rat (f : ℝ →+ ℝ) (q : ℚ) : f q = f 1 * q := by
  have := map_ratCast_smul f ℚ ℚ q (1 : ℝ)
  simpa [mul_comm] using this

theorem additive_isBounded_of_isBounded_on_interval (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a)
    (h : IsBounded (f '' s)) : ∃ V, V ∈ 𝓝 (0 : ℝ) ∧ IsBounded (f '' V) := by
  rcases Metric.mem_nhds_iff.mp hs with ⟨δ, hδ, hδa⟩
  refine ⟨ball 0 δ, ball_mem_nhds 0 hδ, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  simp only [mem_image, mem_ball_zero_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 h
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hM
  refine
    ⟨M + M, fun x hxδ => (norm_le_add_norm_add _ <| f a).trans <| add_le_add ?_ <| hM _ <| hδa ?_⟩
  · rw [← map_add f]
    exact hM _ <| hδa <| by simpa
  · simpa [mem_ball, dist_self]

-- to generalize
theorem AddMonoidHom.continuousAt_iff_continuousAt_zero (f : ℝ →+ ℝ) :
    ContinuousAt f a ↔ ContinuousAt f 0 where
  mp := by
    simp_rw [continuousAt_iff]
    refine forall₂_imp ?_
    rintro ε hε ⟨δ, hδ₀, hδf⟩
    refine ⟨δ, hδ₀, fun {y} hyδ => ?_⟩
    replace hyδ : dist (y + a) a < δ := by simpa [dist_eq_norm] using hyδ
    simpa using hδf hyδ
  mpr h := (continuous_of_continuousAt_zero f h).continuousAt

theorem Continuous.isLinearMap_real (f : ℝ →+ ℝ) (h : Continuous f) : IsLinearMap ℝ f :=
  (f.toRealLinearMap h).isLinear

theorem isLinearMap_real_of_isBounded_nhds (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a) (hf : IsBounded (f '' s)) :
    IsLinearMap ℝ f :=
  let ⟨_V, hV0, hVb⟩ := additive_isBounded_of_isBounded_on_interval f hs hf
  (f.continuous_of_isBounded_nhds_zero hV0 hVb).isLinearMap_real f

theorem MonotoneOn.isLinearMap_real (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a) (hf : MonotoneOn f s) :
    IsLinearMap ℝ f := by
  obtain ⟨t, ht, h⟩ := Metric.mem_nhds_iff.mp hs
  refine isLinearMap_real_of_isBounded_nhds f (closedBall_mem_nhds a <| half_pos ht) ?_
  replace h := (closedBall_subset_ball <| half_lt_self ht).trans h
  rw [Real.closedBall_eq_Icc] at h ⊢
  have ha : a - t / 2 ≤ a + t / 2 := by linarith
  refine isBounded_of_bddAbove_of_bddBelow (hf.map_bddAbove h ?_) (hf.map_bddBelow h ?_)
  · refine ⟨a + t / 2, ?_, h <| right_mem_Icc.2 ha⟩
    rw [upperBounds_Icc ha]
    exact left_mem_Ici
  · refine ⟨a - t / 2, ?_, h <| left_mem_Icc.2 ha⟩
    rw [lowerBounds_Icc ha]
    exact right_mem_Iic
