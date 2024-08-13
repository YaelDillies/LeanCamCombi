/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.LinearAlgebra.AffineSpace.Independent
import LeanCamCombi.Mathlib.Analysis.Convex.SimplicialComplex.Basic
import LeanCamCombi.SimplicialComplex.Simplex

/-!
# Simplicial complexes
-/

open Finset

variable {𝕜 E ι : Type*}

namespace Geometry.SimplicialComplex
section OrderedRing
variable [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {K K₁ K₂ : SimplicialComplex 𝕜 E} {x y : E}
  {s t : Finset E} {A : Set (Finset E)} {m n : ℕ}

/-- The cells of a simplicial complex are its simplices whose dimension matches the one of the
space. -/
def cells (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  {s | s ∈ K ∧ s.card = FiniteDimensional.finrank 𝕜 E + 1}

/-- The subcells of a simplicial complex are its simplices whose cardinality matches the dimension
of the space. They are thus one smaller than cells. -/
def subcells (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  {s | s ∈ K ∧ s.card = FiniteDimensional.finrank 𝕜 E}

lemma disjoint_interiors (hs : s ∈ K) (ht : t ∈ K) (hxs : x ∈ combiInterior 𝕜 s)
    (hxt : x ∈ combiInterior 𝕜 t) : s = t := by
  classical
  by_contra h
  have hst : s ∩ t ⊂ s := by
    use inter_subset_left
    intro H
    exact hxt.2 $ Set.mem_biUnion ⟨H.trans inter_subset_right,
      fun H2 => h $ (H.trans inter_subset_right).antisymm H2⟩ hxs.1
  refine hxs.2 (Set.mem_biUnion hst ?_)
  push_cast
  exact K.inter_subset_convexHull hs ht ⟨hxs.1, hxt.1⟩

lemma disjoint_interiors_aux (hs : s ∈ K) (ht : t ∈ K) (h : s ≠ t) :
    Disjoint (combiInterior 𝕜 s) (combiInterior 𝕜 t) :=
  Set.disjoint_left.2 fun _x hxs hxt => h <| disjoint_interiors hs ht hxs hxt

lemma eq_singleton_of_singleton_mem_combiInterior (hx : {x} ∈ K) (hs : s ∈ K)
    (hxs : x ∈ combiInterior 𝕜 s) : s = {x} := by
  apply disjoint_interiors hs hx hxs
  rw [combiInterior_singleton]
  exact Set.mem_singleton x

lemma combiInteriors_cover : (⋃ s ∈ K, combiInterior 𝕜 s) = K.space := by
  unfold space
  refine (Set.iUnion₂_mono fun _ _ => ?_).antisymm (Set.iUnion₂_subset fun s hs => ?_)
  · exact combiInterior_subset_convexHull
  rw [simplex_combiInteriors_cover]
  refine Set.iUnion₂_mono' fun t hts => ?_
  obtain rfl | ht := t.eq_empty_or_nonempty
  · refine ⟨s, hs, ?_⟩
    rw [combiInterior_empty]
    exact Set.empty_subset _
  · exact ⟨t, K.down_closed' hs hts ht, Set.Subset.rfl⟩

/-- The simplices interiors form a partition of the underlying space (except that they contain the
empty set) -/
lemma combiInteriors_partition (hx : x ∈ K.space) : ∃! s, s ∈ K ∧ x ∈ combiInterior 𝕜 s := by
  rw [← combiInteriors_cover] at hx
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨s, ⟨⟨hs, hxs⟩, fun t ⟨ht, hxt⟩ => disjoint_interiors ht hs hxt hxs⟩⟩

lemma mem_convexHull_iff :
    x ∈ convexHull 𝕜 (s : Set E) ↔ ∃ t, t ⊆ s ∧ x ∈ combiInterior 𝕜 t := by
  simp [simplex_combiInteriors_cover]

lemma mem_combiFrontier_iff' : x ∈ combiFrontier 𝕜 s ↔ ∃ t, t ⊂ s ∧ x ∈ combiInterior 𝕜 t := by
  rw [mem_combiFrontier_iff]
  constructor
  · rintro ⟨t, hts, hxt⟩
    --rw [simplex_combiInteriors_cover, mem_Union₂] at hxt,
    --obtain ⟨u, hu⟩ := simplex_combiInteriors_cover
    sorry
  · rintro ⟨t, hts, hxt⟩
    exact ⟨t, hts, hxt.1⟩

lemma subset_of_combiInterior_inter_convexHull_nonempty (hs : s ∈ K) (ht : t ∈ K)
    (hst : (combiInterior 𝕜 s ∩ convexHull 𝕜 (t : Set E)).Nonempty) : s ⊆ t := by
  obtain ⟨x, hxs, hxt⟩ := hst
  obtain ⟨u, hut, hxu⟩ := mem_convexHull_iff.1 hxt
  rw [disjoint_interiors hs (K.down_closed' ht hut <| nonempty_of_ne_empty _) hxs hxu]
  exact hut
  · rintro rfl
    rwa [combiInterior_empty] at hxu

def dim (K : SimplicialComplex 𝕜 E) : ℕ := sorry

end OrderedRing

section LinearOrderedField
variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {K : SimplicialComplex 𝕜 E} {x y : E}
  {s t : Finset E} {A : Set (Finset E)} {m n : ℕ}

lemma cells_subset_facets [FiniteDimensional 𝕜 E] : K.cells ⊆ K.facets := by
  rintro s ⟨hs, hscard⟩
  by_contra h
  obtain ⟨t, ht, hst⟩ := (not_facet_iff_subface hs).mp h
  have := card_lt_card hst
  have := face_dimension_le_space_dimension ht
  linarith

lemma simplex_combiInteriors_split_interiors (ht : AffineIndependent 𝕜 ((↑) : t → E))
    (hst : convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t) :
    ∃ u, u ⊆ t ∧ combiInterior 𝕜 s ⊆ combiInterior 𝕜 u := by
  classical
  let K := SimplicialComplex.ofSimplex ht
  let F := t.powerset.filter fun v : Finset E => (s : Set E) ⊆ convexHull 𝕜 ↑v
  sorry
/-obtain ⟨u, hu, humin⟩ := inf' _
  (begin
    use t,
    simp only [true_and, mem_powerset_self, mem_filter],
    exact subset.trans (subset_convexHull 𝕜 _) hst,
  end : F.nonempty)
  begin
    rintro A B hA hB,
    simp at ⊢ hA hB,
    exact ⟨subset.trans (inter_subset_left _ _) hA.1,
      subset.trans (subset_inter hA.2 hB.2) (K.disjoint ((mem_simplex_complex_iff ht).2 hA.1)
      ((mem_simplex_complex_iff ht).2 hB.1))⟩
  end,
  simp at hu,
  use [u, hu.1],
  rintro x hxs,
  use convexHull_min hu.2 (convex_convexHull 𝕜 _) hxs.1,
  rintro hxu,
  rw mem_combiFrontier_iff' at hxu,
  obtain ⟨v, hvu, hxv⟩ := hxu,
  apply hvu.2 (humin v _),
  simp,
  use [subset.trans hvu.1 hu.1],
  rw convexHull_eq _ at ⊢ hu,
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combiInterior_subset_positive_weighings hxs,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combiInterior_subset_positive_weighings hxv,
  let u : E → E → 𝕜 := λ a, if ha : a ∈ s then classical.some (hu.2 ha) else (λ b, 0),
  have hupos : ∀ {a}, a ∈ s → ∀ (b : E), b ∈ u → 0 < u a b,
  { rintro a ha,
    have := classical.some_spec (hu.2 ha),
    sorry
  },
  have husum : ∀ {a}, a ∈ s → ∑ (b : E) in u, u a b = 1,
  { sorry
  },
  have hucenter : ∀ {a}, a ∈ s → u.center_mass (u a) id = a,
  { sorry
  },
  let t : E → 𝕜 := λ b, if hb : b ∈ u then ∑ (a : E) in s, v a * u a b else 0,-/
/-rintro y (hys : y ∈ s),
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combiInterior_subset_positive_weighings hxs,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combiInterior_subset_positive_weighings hxv,-/
--rw mem_convexHull,
/-by_contra hsv,
  obtain ⟨y, hys, hyv⟩ := not_subset.1 hsv,-/
/-apply hxs.2,
  rw mem_combiFrontier_iff at ⊢,
  use [s.filter (λ w : E, w ∈ convexHull 𝕜 (v : set E)), filter_subset _ _],
  { rintro hsv,
    apply hvu.2 (humin v _),
    simp,
    use [subset.trans hvu.1 hu.1],
    rintro y (hys : y ∈ s),
    have := hsv hys,
    simp at this,
    exact this.2 },
  { simp,
    apply convexHull_mono (subset_inter (subset.refl _) _) hxs.1, by_contra hsv,
    rw not_subset at hsv,
    /-suffices hsv : ↑s ⊆ convexHull 𝕜 ↑v,
    { apply convexHull_mono (subset_inter (subset.refl _) hsv) hxs.1,
    },-/
    sorry
  }-/

lemma simplex_combiInteriors_split_interiors_nonempty (hs : s.Nonempty)
    (ht : AffineIndependent 𝕜 ((↑) : t → E)) (hst : convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t) :
    ∃ u, u ⊆ t ∧ u.Nonempty ∧ combiInterior 𝕜 s ⊆ combiInterior 𝕜 u := by sorry

end LinearOrderedField
end Geometry.SimplicialComplex
