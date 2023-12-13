/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Order.Basic

/-!
# Extreme sets
-/

open Set

variable {𝕜 E : Type*}

section LinearOrderedField
variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E} {x : E}

lemma Convex.isExtreme_iff_openSegment_subset_diff (hAconv : Convex 𝕜 s) :
    IsExtreme 𝕜 s t ↔ t ⊆ s ∧ ∀ ⦃x y⦄, x ∈ s → y ∈ s \ t → openSegment 𝕜 x y ⊆ s \ t := by
  refine' ⟨fun h => ⟨h.1, fun x y hx hy z hz =>
    ⟨hAconv.openSegment_subset hx hy.1 hz, fun hzB => hy.2 (h.2 hx hy.1 hzB hz).2⟩⟩,
      fun h => ⟨h.1, fun x hx y hy z hzB hz => ⟨_, _⟩⟩⟩
  · by_contra hxB
    rw [openSegment_symm] at hz
    exact (h.2 hy ⟨hx, hxB⟩ hz).2 hzB
  · by_contra hyB
    exact (h.2 hx ⟨hy, hyB⟩ hz).2 hzB

lemma extremePoints_convexHull_eq_iff_convexIndependent :
    (convexHull 𝕜 s).extremePoints 𝕜 = s ↔ ConvexIndependent 𝕜 (fun p => p : s → E) := by
  refine' ⟨fun h => _, fun hs => _⟩
  · rw [← h]
    exact (convex_convexHull 𝕜 _).convexIndependent_extremePoints
  rw [convexIndependent_set_iff_not_mem_convexHull_diff] at hs
  refine' extremePoints_convexHull_subset.antisymm fun x hxs => ⟨subset_convexHull 𝕜 _ hxs, _⟩
  by_contra! h
  obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := h
  suffices h : x₁ ∈ convexHull 𝕜 (s \ {x}) ∧ x₂ ∈ convexHull 𝕜 (s \ {x})
  · exact hs _ hxs (convex_iff_openSegment_subset.1 (convex_convexHull 𝕜 _) h.1 h.2 hx.1)
  have hx₁₂ : segment 𝕜 x₁ x₂ ⊆ convexHull 𝕜 s := (convex_convexHull 𝕜 _).segment_subset hx₁ hx₂
  -- rw convexHull_eq at hx₁ hx₂,
  -- obtain ⟨ι₁, t₁, w₁, z₁, hw₁₀, hw₁₁, hz₁, rfl⟩ := hx₁,
  -- obtain ⟨ι₂, t₂, w₂, z₂, hw₂₀, hw₂₁, hz₂, rfl⟩ := hx₂,
  sorry

-- refine ⟨erase_subset_convexHull_erase hx₁₂ (subset_convexHull 𝕜 _ $
--   open_segment_subset_segment _ _ hx.1) _, erase_subset_convexHull_erase hx₁₂
--   (subset_convexHull 𝕜 _ $ open_segment_subset_segment _ _ hx.1) _⟩,
-- { rw [mem_diff, mem_singleton_iff],
--   refine ⟨left_mem_segment _ _, λ h, hx.2 h _⟩,
--   rw [h, left_mem_open_segment_iff] at hx,
--   exact hx.1.symm },
-- rw [mem_diff, mem_singleton_iff],
-- refine ⟨right_mem_segment _ _, λ h, hx.2 _ h⟩,
-- rw [h, right_mem_open_segment_iff] at hx,
-- exact hx.1,
end LinearOrderedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {s t : Set E}
  {x : E}

-- beurk
lemma inter_frontier_self_inter_convexHull_extreme :
    IsExtreme 𝕜 (closure s) (closure s ∩ frontier (convexHull 𝕜 s)) := by
  refine' ⟨inter_subset_left _ _, fun x₁ hx₁A x₂ hx₂A x hxs hx => ⟨⟨hx₁A, _⟩, hx₂A, _⟩⟩
  sorry
  sorry

-- beurk
lemma frontier_extreme (hA₁ : Convex 𝕜 s) (hA₂ : IsClosed s) : IsExtreme 𝕜 s (frontier s) := by
  convert
    (inter_frontier_self_inter_convexHull_extreme :
      IsExtreme 𝕜 (closure s) (closure s ∩ frontier (convexHull 𝕜 s))) using 1
  · exact (IsClosed.closure_eq hA₂).symm
  rw [Convex.convexHull_eq hA₁, inter_eq_self_of_subset_right frontier_subset_closure]

-- interesting
lemma Convex.frontier_extreme_to_closure (hAconv : Convex 𝕜 s) :
    IsExtreme 𝕜 (closure s) (frontier s) := by
  use frontier_subset_closure
  sorry

--can be generalized is_extreme.subset_intrinsic_frontier
lemma IsExtreme.subset_frontier (hAB : IsExtreme 𝕜 s t) (hBA : ¬s ⊆ t) : t ⊆ frontier s := by
  rintro x hxB
  obtain ⟨y, hyA, hyB⟩ := nonempty_of_ssubset ⟨hAB.1, hBA⟩
  rw [frontier_eq_closure_inter_closure]
  use subset_closure (hAB.1 hxB)
  rw [mem_closure_iff_seq_limit]
  let z : ℕ → E := fun n => (1 + 1 / n.succ : 𝕜) • x - (1 / n.succ : 𝕜) • y
  use z
  /-
    split,
    { rintro n hzn,
      --have := hAB.2 y (f n) hyA hfn x hxB,
      refine hyB (hAB.2 y (z n) hyA hzn x hxB ⟨1/(↑n + 1)/(1/(↑n + 1) + 1), 1/(1/(↑n + 1) + 1),
        _, _, _, _⟩).1,
      { exact (div_pos nat.one_div_pos_of_nat (add_pos nat.one_div_pos_of_nat (by linarith))).le },
      { exact le_of_lt (one_div_pos.2 (add_pos nat.one_div_pos_of_nat (by linarith))).le },
      { rw [←add_div, div_self],
        exact (add_pos nat.one_div_pos_of_nat (by linarith)).ne' },
      {   sorry,
      },
      { rintro rfl,
        exact hyB hxB },
      { rintro h,
        apply hyB,
        suffices h : x = y,
        { rw ←h, exact hxB },
        suffices h : (1/n.succ : ℝ) • x = (1/n.succ : ℝ) • y,
        { exact smul_injective (ne_of_gt nat.one_div_pos_of_nat) h },
        calc
          (1/n.succ : ℝ) • x
              = -(1 • x) + ((1 • x + (1/n.succ : ℝ) • x) - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y
              : sorry
          ... = -(1 • x) + ((1 + 1/n.succ : ℝ) • x - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y : sorry
          ... = -(1 • x) + z n + (1/n.succ : ℝ) • y : by refl
          ... = -(1 • x) + x + (1/n.succ : ℝ) • y : by rw h
          ... = (1/n.succ : ℝ) • y : by simp } },
    rw ←sub_zero x,
    apply filter.tendsto.sub,
    { nth_rewrite 0 ←one_smul _ x,
      apply filter.tendsto.smul_const,
      nth_rewrite 0 ←add_zero (1 : ℝ), --weirdly skips the first two `1`. Might break in the future
      apply filter.tendsto.const_add,
      sorry },
    rw ←zero_smul _ y,
    apply filter.tendsto.smul_const,-/
  sorry

/-{E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [sequential_space E] [topological_add_group E] [has_continuous_smul ℝ E]-/
lemma closure_eq_closure_interior {s : Set E} (hAconv : Convex 𝕜 s)
    (hAnemp : (interior s).Nonempty) : closure s = closure (interior s) := by
  refine' Subset.antisymm (fun x hx => _) (closure_mono interior_subset)
  obtain ⟨y, hy⟩ := hAnemp
  rw [mem_closure_iff_seq_limit] at hx ⊢
  obtain ⟨z, hzA, hzx⟩ := hx
  refine' ⟨fun n => (1 - 1 / (n + 2) : 𝕜) • z n + (1 / (n + 2) : 𝕜) • y, fun n => _, _⟩
  · rw [← closure_diff_frontier] at hy ⊢
    have h₁ : (1 : 𝕜) < ↑n + 2 := by norm_cast; norm_num
    have h₀ := zero_lt_one.trans h₁
    exact
      (hAconv.closure.isExtreme_iff_openSegment_subset_diff.1
            hAconv.frontier_extreme_to_closure).2
        (subset_closure (hzA n)) hy
        ⟨1 - 1 / (n + 2), 1 / (n + 2), sub_pos.2 <| (div_lt_one h₀).2 h₁, div_pos zero_lt_one h₀,
          sub_add_cancel _ _, rfl⟩
  have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : 𝕜) + 2)) Filter.atTop (nhds (0 : 𝕜)) := by sorry
  rw [← add_zero x, ← one_smul 𝕜 x, ← zero_smul 𝕜 y]
  convert ((h.const_sub _).smul hzx).add (h.smul_const _)
  rw [sub_zero]

lemma ConvexIndependent.subset_of_convexHull_eq_convexHull {s t : Finset E}
    (hs : ConvexIndependent 𝕜 ((↑) : s → E)) (h : convexHull 𝕜 ↑s = convexHull 𝕜 (t : Set E)) :
    s ⊆ t := by
  rintro x hx
  have hxextreme := (extremePoints_convexHull_eq_iff_convexIndependent.2 hs).symm.subset hx
  erw [h] at hxextreme
  exact_mod_cast extremePoints_convexHull_subset hxextreme

lemma ConvexIndependent.eq_of_convexHull_eq_convexHull {s t : Finset E}
    (hs : ConvexIndependent 𝕜 ((↑) : s → E))
    (ht : ConvexIndependent 𝕜 ((↑) : t → E))
    (h : convexHull 𝕜 (s : Set E) = convexHull 𝕜 (t : Set E)) : s = t :=
  (hs.subset_of_convexHull_eq_convexHull h).antisymm <| ht.subset_of_convexHull_eq_convexHull h.symm

/- deprecated because generalised by `extremePoints_convexHull_eq_iff_convexIndependent`
lemma extreme_to_convexHull_of_affine_independent {s : finset E} (hx : x ∈ s)
  (hs : affine_independent 𝕜 (λ p, p : (s : set E) → E)) :
  x ∈ (convexHull 𝕜 ↑s : set E).extreme_points :=
begin
  refine ⟨subset_convexHull 𝕜 _ hx, _⟩,
  rintro y y' hy hy' t,
  rw finset.convexHull_eq at hy hy',
  obtain ⟨w, hw₀, hw₁, hy⟩ := hy,
  obtain ⟨w', hw'₀, hw'₁, hy'⟩ := hy',
  rw segment_eq_image at t,
  obtain ⟨θ, hθ₁, hθ₂ : _ + _ = _⟩ := t,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hy,
  rw finset.center_mass_eq_of_sum_1 _ _ hw'₁ at hy',
  change s.sum (λ i, w i • i) = y at hy,
  change s.sum (λ i, w' i • i) = y' at hy',
  let w'' : E → ℝ := λ t, (1 - θ) * w t + θ * w' t - if t = x then 1 else 0,
  have hw''₁ : s.sum w'' = 0,
  { rw [finset.sum_sub_distrib, finset.sum_add_distrib, ← finset.mul_sum, ← finset.mul_sum, hw₁,
      hw'₁, finset.sum_ite_eq' s, if_pos hx],
    simp },
  have hw''₂ : s.sum (λ i, w'' i • i) = 0,
  { simp only [sub_smul, add_smul, finset.sum_add_distrib, finset.sum_sub_distrib],
    simp only [mul_smul, ←finset.smul_sum, hy, hy'],
    simp only [ite_smul, zero_smul, one_smul, finset.sum_ite_eq', if_pos hx, hθ₂, sub_self] }, by_contra t,
  push_neg at t,
  suffices hw''₃ : ∀ q ∈ s, w'' q = 0,
  { have : θ = 0 ∨ θ = 1,
    { by_contra hθ,
      push_neg at hθ,
      have : 0 < θ ∧ 0 < 1 - θ,
      { split,
        { apply lt_of_le_of_ne hθ₁.1 hθ.1.symm },
        { rw sub_pos,
          apply lt_of_le_of_ne hθ₁.2 hθ.2 } },
      have both_zero : ∀ q ∈ s, q ≠ x → w q = 0,
      { intros q hq₁ hq₂,
        specialize hw''₃ q hq₁,
        change _ + _ = _ at hw''₃,
        rw if_neg hq₂ at hw''₃,
        simp only [add_zero, neg_zero] at hw''₃,
        rw add_eq_zero_iff'
            (mul_nonneg (le_of_lt this.2) (hw₀ q hq₁))
            (mul_nonneg (le_of_lt this.1) (hw'₀ q hq₁)) at hw''₃,
        rw mul_eq_zero at hw''₃,
        apply or.resolve_left hw''₃.1 (ne_of_gt this.2) },
      have : (1 - θ) * w x + θ * w' x = 1,
      { specialize hw''₃ _ hx,
        change (1 - θ) * w x + θ * w' x - ite _ _ _ = 0 at hw''₃,
        rwa [if_pos rfl, sub_eq_zero] at hw''₃ },
      rw finset.sum_eq_single x at hw₁,
      { rw finset.sum_eq_single x at hy,
        { rw hw₁ at hy,
          apply t.1,
          rw ←hy,
          simp },
        { rintro q hq₁ hq₂,
          rw both_zero q hq₁ hq₂,
          simp },
        { exact λ t, (t hx).elim } },
      { intros q hq₁ hq₂,
        apply both_zero q hq₁ hq₂ },
      { exact λ t, (t hx).elim } },
    rcases this with (rfl | rfl),
    { simp only [add_zero, one_smul, sub_zero, zero_smul] at hθ₂,
      apply t.1 hθ₂.symm },
    { simp only [one_smul, zero_smul, zero_add, sub_self] at hθ₂,
      apply t.2 hθ₂.symm } },
  rw affine_independent_iff_of_fintype at hs,
  let w''' : (s : set E) → ℝ := λ t, w'' (t : E),
  have hw''' : finset.univ.sum w''' = 0,
  { rw coe_sum,
    apply hw''₁ },
  specialize hs w''' hw''' _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw''' (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    rw coe_sum _ (λ i, w'' i • i),
    apply hw''₂ },
  rintro q hq,
  exact hs ⟨q, hq⟩,
end
-/
end NormedLinearOrderedField
