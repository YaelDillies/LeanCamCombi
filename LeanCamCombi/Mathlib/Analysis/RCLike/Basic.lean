import Mathlib.Analysis.RCLike.Basic

open Bornology Metric Set
open scoped Topology

variable {G K : Type*} [SeminormedAddCommGroup G] [TopologicalAddGroup G] [RCLike K] {s : Set G}

theorem AddMonoidHom.continuous_of_isBounded_nhds_zero (f : G →+ K) (hs : s ∈ 𝓝 (0 : G))
    (hbounded : IsBounded (f '' s)) : Continuous f := by
  obtain ⟨δ, hδ, hUε⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨C, hC⟩ := (isBounded_iff_subset_ball 0).1 (hbounded.subset <| image_subset f hUε)
  refine continuous_of_continuousAt_zero _ (continuousAt_iff.2 fun ε (hε : _ < _) => ?_)
  simp only [dist_zero_right, _root_.map_zero, exists_prop]
  simp only [subset_def, mem_image, mem_ball, dist_zero_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hC
  have hC₀ : 0 < C := (norm_nonneg _).trans_lt <| hC 0 (by simpa)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hnpos : 0 < (n : ℝ) := (div_pos hC₀ hε).trans hn
  refine ⟨δ / n, div_pos hδ hnpos, fun {x} hxδ => ?_⟩
  have h2 : f (n • x) = n • f x := map_nsmul f _ _
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simp at hnpos)
  simp_rw [nsmul_eq_mul, mul_comm (n : K), ← div_eq_iff hn'] at h2
  replace hxδ : ‖n • x‖ < δ := by
    refine norm_nsmul_le.trans_lt ?_
    simpa only [norm_mul, Real.norm_natCast, lt_div_iff₀ hnpos, mul_comm] using hxδ
  rw [← h2, norm_div, RCLike.norm_natCast, div_lt_iff₀' hnpos]
  rw [div_lt_iff₀ hε] at hn
  exact (hC _ hxδ).trans hn
