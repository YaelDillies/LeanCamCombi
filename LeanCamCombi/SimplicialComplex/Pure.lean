/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Finset.Slice
import LeanCamCombi.SimplicialComplex.Basic

/-!
# Pure simplicial complexes
-/

open Finset

variable {𝕜 E : Type*}

namespace Geometry.SimplicialComplex
section OrderedRing
variable [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {a b n k : ℕ} {K : SimplicialComplex 𝕜 E}
  {s : Finset E}

/-- A simplicial complex is pure of dimension `n` iff all its faces have dimension less `n` and its
facets have dimension `n`. -/
def Pure (K : SimplicialComplex 𝕜 E) (n : ℕ) : Prop :=
  (∀ ⦃s : Finset E⦄, s ∈ K → s.card ≤ n + 1) ∧ K.facets.Sized (n + 1)

def FullDimensional (K : SimplicialComplex 𝕜 E) : Prop := K.Pure (K.dim + 1)

lemma Pure.card_le (hK : K.Pure n) (hs : s ∈ K) : s.card ≤ n + 1 := hK.1 hs
lemma Pure.sized_facets (hK : K.Pure n) : K.facets.Sized (n + 1) := hK.2

lemma botPure (n : ℕ) : (⊥ : SimplicialComplex 𝕜 E).Pure n :=
  ⟨fun _s hs => hs.elim, fun _s hs => hs.1.elim⟩

lemma Pure.exists_facet (hK : K.Pure n) (hs : s ∈ K) : ∃ t ∈ K.facets, s ⊆ t := by sorry

lemma Pure.exists_face_of_card_le (hK : K.Pure n) (h : k ≤ n + 1) (hs : s ∈ K)
    (hcard : s.card ≤ k) : ∃ t ∈ K, s ⊆ t ∧ t.card = k := by
  by_cases H : s ∈ K.facets
  · exact ⟨s, hs, Subset.rfl, hcard.antisymm <| h.trans (hK.2 H).ge⟩
  · unfold facets at H
    simp at H
    sorry

lemma pure_unique (hK : K.faces.Nonempty) (ha : K.Pure a) (hb : K.Pure b) : a = b := by
  obtain ⟨s, hs⟩ := hK
  obtain ⟨t, ht, -⟩ := ha.exists_facet hs
  exact add_right_cancel ((ha.2 ht).symm.trans <| hb.2 ht)

lemma Pure.mem_facets_iff (hK : K.Pure n) (hs : s ∈ K) : s ∈ K.facets ↔ s.card = n + 1 :=
  ⟨fun hsfacet => hK.2 hsfacet, fun hscard =>
    ⟨hs, fun _t ht hst => Finset.eq_of_subset_of_card_le hst <| (hK.card_le ht).trans hscard.ge⟩⟩

/-- A simplicial complex is pure iff there exists `n` such that all faces are subfaces of some
`n`-dimensional face. -/
lemma pure_iff : K.Pure n ↔ ∀ ⦃s⦄, s ∈ K → ∃ t ∈ K, Finset.card t = n + 1 ∧ s ⊆ t := by
  refine ⟨fun hK s hs => ?_, fun hK => ⟨fun s hs => ?_, fun s hs => ?_⟩⟩
  · obtain ⟨t, ht, hst⟩ := hK.exists_facet hs
    exact ⟨t, ht.1, hK.2 ht, hst⟩
  · obtain ⟨t, _, htcard, hst⟩ := hK hs
    exact (Finset.card_le_card hst).trans_eq htcard
  · obtain ⟨t, ht, htcard, hst⟩ := hK hs.1
    rwa [hs.2 ht hst]

lemma facets_mono {K₁ K₂ : SimplicialComplex 𝕜 E} (h : K₁ ≤ K₂) (hK₁ : K₁.Pure n)
    (hK₂ : K₂.Pure n) : K₁.facets ⊆ K₂.facets := by
  refine fun s hs => ⟨h hs.1, fun t ht hst => Finset.eq_of_subset_of_card_le hst ?_⟩
  rw [hK₁.2 hs]
  exact hK₂.card_le ht

end OrderedRing

end Geometry.SimplicialComplex
