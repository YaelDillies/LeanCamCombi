/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import LeanCamCombi.SimplicialComplex.Pure

/-!
# Skeleton of a simplicial complex
-/

open Finset Geometry

variable {𝕜 E : Type*}

namespace Geometry.SimplicialComplex

section OrderedRing

variable [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {m n k : ℕ} {K : SimplicialComplex 𝕜 E}
  {s t : Finset E} {A : Set (Finset E)}

/-- The `k`-skeleton of a simplicial complex is the simplicial complex made of its simplices of
dimension less than `k`. -/
def skeleton (K : SimplicialComplex 𝕜 E) (k : ℕ) : SimplicialComplex 𝕜 E :=
  K.ofSubcomplex' {s | s ∈ K ∧ #s ≤ k + 1} (fun _s ⟨hs, _⟩ => hs) fun _s _t hs hts ht =>
    ⟨K.down_closed' hs.1 hts ht, (card_le_card hts).trans hs.2⟩

lemma skeleton_le : K.skeleton k ≤ K := K.ofSubcomplex_le _
lemma skeleton_bot (k : ℕ) : (⊥ : SimplicialComplex 𝕜 E).skeleton k = ⊥ := ofSubcomplex_bot _

lemma skeleton_nonempty_iff : (K.skeleton k).faces.Nonempty ↔ K.faces.Nonempty := by
  refine ⟨Set.Nonempty.mono skeleton_le, ?_⟩
  rintro ⟨s, hs⟩
  obtain ⟨x, hx⟩ := K.nonempty hs
  refine ⟨{x}, K.down_closed' hs (singleton_subset_iff.2 hx) <| singleton_nonempty _, ?_⟩
  rw [card_singleton]
  exact le_add_self

lemma Pure.skeleton_of_le (hK : K.Pure n) (h : k ≤ n) : (K.skeleton k).Pure k := by
  refine ⟨fun s hs => hs.2, ?_⟩
  rintro s ⟨⟨hs, hscard⟩, hsmax⟩
  obtain ⟨t, ht, hst, htcard⟩ := hK.exists_face_of_card_le (add_le_add_right h 1) hs hscard
  rwa [hsmax ⟨ht, htcard.le⟩ hst]

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E] {m n k : ℕ}
  {K : SimplicialComplex 𝕜 E} {s t : Finset E} {A : Set (Finset E)}

lemma Pure.skeleton (hK : K.Pure n) : (K.skeleton k).Pure (min k n) := by
  obtain hn | hn := le_total k n
  · rw [min_eq_left hn]
    exact hK.skeleton_of_le hn
  · rw [min_eq_right hn]
    refine ⟨fun s hs => hK.1 <| skeleton_le hs, fun s hs => ?_⟩
    obtain ⟨t, ht, hst⟩ := subfacet (skeleton_le hs.1)
    rw [hs.2 ⟨facets_subset ht, (hK.2 ht).le.trans (add_le_add_right hn _)⟩ hst]
    exact hK.2 ht

end LinearOrderedField
end Geometry.SimplicialComplex
