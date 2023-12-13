/-
Copyright (c) 2021 Yaël Dillies, thavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, thavik Mehta
-/
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import LeanCamCombi.Mathlib.Analysis.Convex.Extreme

/-!
# Exposed sets
-/

open Set

--TODO: Generalise to LCTVS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {s t C : Set E}
  {X : Finset E} {l : E →L[ℝ] ℝ}

namespace IsExposed

lemma subset_frontier (hst : IsExposed ℝ s t) (hts : ¬s ⊆ t) : t ⊆ frontier s :=
  hst.isExtreme.subset_frontier hts

lemma span_lt (hst : IsExposed ℝ s t) (hts : ¬s ⊆ t) : affineSpan ℝ t < affineSpan ℝ s := by
  apply (affineSpan_mono _ hst.subset).lt_of_ne
  rintro h
  sorry

end IsExposed

/-lemma is_exposed.dim_lt (hst : is_exposed s t) (hts : ¬ s ⊆ t) :
  (affine_span ℝ t).rank < (affine_span ℝ s).rank :=
begin

end-/
lemma mem_exposed_set_iff_mem_frontier (hs₁ : Convex ℝ s) (hs₂ : (interior s).Nonempty) :
    (∃ t : Set E, IsExposed ℝ s t ∧ ¬s ⊆ t ∧ x ∈ t) ↔ x ∈ s ∧ x ∈ frontier s := by
  use fun ⟨t, hst, hts, hxt⟩ => ⟨hst.subset hxt, hst.subset_frontier hts hxt⟩
  rintro ⟨hxA, hxfA⟩
  obtain ⟨y, hyA⟩ := id hs₂
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point (Convex.interior hs₁) isOpen_interior hxfA.2
  refine'
    ⟨{x ∈ s | ∀ y ∈ s, l y ≤ l x}, fun _ => ⟨l, rfl⟩, fun h =>
      not_le.2 (hl y hyA) ((h (interior_subset hyA)).2 x hxA), hxA, fun z hzA => _⟩
  suffices h : l '' closure (interior s) ⊆ closure (Iio (l x))
  · rw [closure_Iio, ← closure_eq_closure_interior hs₁ hs₂] at h
    exact h ⟨z, subset_closure hzA, rfl⟩
  refine' (image_closure_subset_closure_image l.continuous).trans $ closure_mono _
  rintro _ ⟨w, hw, rfl⟩
  exact hl w hw

lemma mem_extreme_set_iff_mem_frontier (hs₁ : Convex ℝ s) (hs₂ : (interior s).Nonempty) :
    (∃ t : Set E, IsExtreme ℝ s t ∧ ¬s ⊆ t ∧ x ∈ t) ↔ x ∈ s ∧ x ∈ frontier s := by
  use fun ⟨t, hst, hts, hxt⟩ => ⟨hst.1 hxt, hst.subset_frontier hts hxt⟩
  rintro h
  obtain ⟨t, hst, hts, hxt⟩ := (mem_exposed_set_iff_mem_frontier hs₁ hs₂).2 h
  exact ⟨t, hst.isExtreme, hts, hxt⟩

/-! # Harder stuff -/



--lemma of S. Straszewicz proved in 1935
lemma extremePoints_subset_closure_exposedPoints (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    s.extremePoints ℝ ⊆ closure (s.exposedPoints ℝ) := by sorry
