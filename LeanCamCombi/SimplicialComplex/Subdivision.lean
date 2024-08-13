/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.SpecificLimits.Basic
import LeanCamCombi.SimplicialComplex.Basic

/-!
# Subdivision of simplicial complexes
-/

open Geometry Finset Set

variable {𝕜 E : Type*}

namespace Geometry.SimplicialComplex

section OrderedRing

variable [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {m : ℕ} {K K₁ K₂ K₃ : SimplicialComplex 𝕜 E}

/-- `K₁` is a subdivision of `K₂` iff their underlying space is the same and each face of `K₁` is
contained in some face of `K₂`. -/
def Subdivides (K₁ K₂ : SimplicialComplex 𝕜 E) : Prop :=
  K₁.space = K₂.space ∧
    ∀ ⦃s₁⦄, s₁ ∈ K₁ → ∃ s₂ ∈ K₂, convexHull 𝕜 (s₁ : Set E) ⊆ convexHull 𝕜 (s₂ : Set E)

@[refl]
lemma Subdivides.refl (K : SimplicialComplex 𝕜 E) : K.Subdivides K :=
  ⟨rfl, fun s hs => ⟨s, hs, Subset.rfl⟩⟩

lemma Subdivides.rfl : K.Subdivides K :=
  Subdivides.refl _

@[trans]
lemma Subdivides.trans (h₁₂ : K₁.Subdivides K₂) (h₂₃ : K₂.Subdivides K₃) : K₁.Subdivides K₃ :=
  ⟨h₁₂.1.trans h₂₃.1, fun _s₁ hs₁ =>
    let ⟨_s₂, hs₂, hs₁₂⟩ := h₁₂.2 hs₁
    let ⟨s₃, hs₃, hs₂₃⟩ := h₂₃.2 hs₂
    ⟨s₃, hs₃, hs₁₂.trans hs₂₃⟩⟩

end OrderedRing

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E] [T2Space E] [NormedSpace ℝ E] {s t : Finset E} {m : ℕ}
  {K₁ K₂ : SimplicialComplex ℝ E}

lemma subdivides_iff_combiInteriors_subset_combiInteriors :
    K₁.Subdivides K₂ ↔
      K₂.space ⊆ K₁.space ∧ ∀ s₁ ∈ K₁, ∃ s₂ ∈ K₂, combiInterior ℝ s₁ ⊆ combiInterior ℝ s₂ := by
  refine ⟨fun h => ⟨h.1.superset, fun s hs => ?_⟩, fun h =>
    ⟨h.1.antisymm' fun x hx => ?_, fun s₁ hs₁ => ?_⟩⟩
  · obtain ⟨t, ht, hst⟩ := h.2 hs
    obtain ⟨u, hut, hu, hsu⟩ :=
      simplex_combiInteriors_split_interiors_nonempty (K₁.nonempty hs) (K₂.indep ht) hst
    exact ⟨u, K₂.down_closed' ht hut hu, hsu⟩
  · obtain ⟨s₁, hs₁, hx⟩ := mem_space_iff.1 hx
    obtain ⟨s₂, hs₂, hs₁s₂⟩ := h.2 _ hs₁
    rw [mem_space_iff]
    exact ⟨s₂, hs₂, convexHull_subset_convexHull_of_combiInterior_subset_combiInterior
      (K₁.indep hs₁) (K₂.indep hs₂) hs₁s₂ hx⟩
  · obtain ⟨s₂, hs₂, hs₁s₂⟩ := h.2 _ hs₁
    exact ⟨_, hs₂, convexHull_subset_convexHull_of_combiInterior_subset_combiInterior (K₁.indep hs₁)
      (K₂.indep hs₂) hs₁s₂⟩

lemma subdivides_iff_partition :
    K₁.Subdivides K₂ ↔ (K₁.faces.Nonempty → K₂.faces.Nonempty) ∧ K₁.space ⊆ K₂.space ∧
      ∀ s₂ ∈ K₂, ∃ F, F ⊆ K₁.faces ∧ combiInterior ℝ s₂ = ⋃ s₁ ∈ F, combiInterior ℝ s₁ := by
  constructor
  · rintro ⟨hspace, hsubdiv⟩
    refine ⟨?_, hspace.le, fun s hs => ?_⟩
    · rintro ⟨s₁, hs₁⟩
      obtain ⟨s₂, hs₂, -⟩ := hsubdiv hs₁
      exact ⟨s₂, hs₂⟩
    refine ⟨{t | t ∈ K₁ ∧ combiInterior ℝ t ⊆ combiInterior ℝ s}, fun t ht => ht.1, ?_⟩
    ext x
    refine ⟨fun hxs => ?_, ?_⟩
    · have hxspace := mem_space_iff.2 ⟨s, hs, hxs.1⟩
      rw [← hspace, ← combiInteriors_cover, mem_iUnion₂] at hxspace
      obtain ⟨t, ht, hxt⟩ := hxspace
      refine mem_iUnion₂_of_mem ⟨ht, fun y hyt => ?_⟩ hxt
      obtain ⟨u, hu, htu⟩ := hsubdiv ht
      obtain ⟨W, hWu, htW⟩ := simplex_combiInteriors_split_interiors (K₂.indep hu) htu
      rw [disjoint_interiors hs (K₂.down_closed hu hWu _) hxs (htW hxt)]
      exact htW hyt
      rintro rfl
      have := htW hxt
      simp at this
    · rw [mem_iUnion₂]
      rintro ⟨t, ⟨-, hts⟩, hxt⟩
      exact hts hxt
  · rintro ⟨hempty, hspace, hpartition⟩
    have hspace : K₁.space = K₂.space := by
      refine hspace.antisymm fun x hx => ?_
      rw [← combiInteriors_cover, mem_iUnion₂] at hx ⊢
      obtain ⟨s, hs, hxs⟩ := hx
      obtain ⟨F, hF, hsint⟩ := hpartition _ hs
      rw [hsint, mem_iUnion₂] at hxs
      obtain ⟨t, ht, hxt⟩ := hxs
      exact ⟨t, hF ht, hxt⟩
    refine ⟨hspace, fun s hs => ?_⟩
    obtain rfl | hsnonempty := s.eq_empty_or_nonempty
    · obtain ⟨t, ht⟩ := hempty ⟨_, hs⟩
      exact ⟨t, ht, by simp⟩
    obtain ⟨x, hx⟩ := hsnonempty.combiInterior (K₁.indep hs)
    have hxspace := mem_space_iff.2 ⟨s, hs, hx.1⟩
    rw [hspace, ← combiInteriors_cover, mem_iUnion₂] at hxspace
    obtain ⟨t, ht, hxt⟩ := hxspace
    use t, ht
    rw [← closure_combiInterior_eq_convexHull (K₁.indep hs)]
    refine closure_minimal (fun x' hx' => ?_) (isClosed_convexHull _)
    have hxspace := mem_space_iff.2 ⟨s, hs, hx'.1⟩
    rw [hspace, ← combiInteriors_cover, mem_iUnion₂] at hxspace
    obtain ⟨t', ht', hxt'⟩ := hxspace
    convert hxt'.1
    obtain ⟨F, hF, hinterior⟩ := hpartition _ ht
    obtain ⟨F', hF', hinterior'⟩ := hpartition _ ht'
    apply disjoint_interiors ht ht' (_ : x ∈ _) _
    · rw [hinterior, mem_iUnion₂] at hxt ⊢
      obtain ⟨u, hu, hxu⟩ := hxt
      exact ⟨u, hu, hxu⟩
    · rw [hinterior', mem_iUnion₂] at hxt' ⊢
      obtain ⟨u, hu, hxu⟩ := hxt'
      refine ⟨u, hu, ?_⟩
      rw [← disjoint_interiors hs (hF' hu) hx' hxu]
      exact hx

instance : IsPartialOrder (SimplicialComplex ℝ E) Subdivides where
  refl := Subdivides.refl
  trans K₁ K₂ K₃ := Subdivides.trans
  antisymm := by
    suffices aux_lemma :
      ∀ {K₁ K₂ : SimplicialComplex ℝ E},
        K₁.Subdivides K₂ → K₂.Subdivides K₁ → ∀ {s}, s ∈ K₁.faces → s ∈ K₂.faces by
      rintro K₁ K₂ h₁ h₂
      ext s
      exact ⟨fun hs => aux_lemma h₁ h₂ hs, fun hs => aux_lemma h₂ h₁ hs⟩
    rintro K₁ K₂ h₁ h₂ s hs
    rw [subdivides_iff_partition] at h₂ h₁
    obtain ⟨x, hxs⟩ := (K₁.nonempty hs).combiInterior (K₁.indep hs)
    obtain ⟨F, hF, hFs⟩ := h₂.2.2 _ hs
    have hxs' := hxs
    rw [hFs, mem_iUnion₂] at hxs'
    obtain ⟨t, ht, hxt⟩ := hxs'
    obtain ⟨F', hF', hF't⟩ := h₁.2.2 _ (hF ht)
    rw [hF't, mem_iUnion₂] at hxt
    obtain ⟨u, hu, hxu⟩ := hxt
    obtain rfl := disjoint_interiors hs (hF' hu) hxs hxu
    convert hF ht
    refine combiInterior.inj (K₁.indep hs) (K₂.indep <| hF ht) (Subset.antisymm ?_ ?_)
    · rw [hF't]
      exact subset_biUnion_of_mem hu
    · rw [hFs]
      exact subset_biUnion_of_mem ht

end SeminormedAddCommGroup

-- /-- max diameter of simplices -/
-- def SimplicialComplex.mesh_size (S : SimplicialComplex 𝕜 E) : 𝕜 := sorry

-- def barycentrisation : list (fin m → 𝕜) → fin m → 𝕜 :=
--   λ L,

-- def SimplicialComplex.barycentricSubdivision (S : SimplicialComplex 𝕜 E) :
--   SimplicialComplex 𝕜 E :=
-- { faces := {s | ∃ {L : list (fin m → 𝕜)}, list.to_finset L ∈ S.faces ∧ s = },
--   indep := _,
--   down_closed := _,
--   disjoint := _ }

end Geometry.SimplicialComplex
