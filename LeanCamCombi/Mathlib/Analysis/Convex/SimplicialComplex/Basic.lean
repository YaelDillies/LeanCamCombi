import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import LeanCamCombi.Mathlib.Analysis.Convex.Combination
import LeanCamCombi.Mathlib.LinearAlgebra.AffineSpace.Independent
import LeanCamCombi.Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Finset Geometry
open scoped Affine BigOperators Classical

variable {𝕜 E ι : Type*}

namespace Geometry.SimplicialComplex
section OrderedRing

variable [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {K K₁ K₂ : SimplicialComplex 𝕜 E} {x y : E}
  {s t : Finset E} {A : Set (Finset E)} {m n : ℕ}

-- TODO: Rename `faces` to `carrier`
instance : SetLike (SimplicialComplex 𝕜 E) (Finset E) where
  coe := faces
  coe_injective' K₁ K₂ hK := by cases K₁; cases K₂; congr

attribute [simp] faces_bot space_bot facets_bot

protected lemma nonempty (K : SimplicialComplex 𝕜 E) (hs : s ∈ K) : s.Nonempty :=
  nonempty_of_ne_empty <| ne_of_mem_of_not_mem hs K.not_empty_mem

--TODO: Replace `down_closed`
protected lemma down_closed' (K : SimplicialComplex 𝕜 E) (hs : s ∈ K.faces) (hts : t ⊆ s)
    (ht : t.Nonempty) : t ∈ K.faces :=
  K.down_closed hs hts ht.ne_empty

@[simp]
lemma mem_faces_iff (K : SimplicialComplex 𝕜 E) : s ∈ K.faces ↔ s ∈ K :=
  Iff.rfl

@[simp]
lemma not_mem_bot : s ∉ (⊥ : SimplicialComplex 𝕜 E) := by simp [← mem_faces_iff]

lemma le_def : K₁ ≤ K₂ ↔ K₁.faces ⊆ K₂.faces :=
  Iff.rfl

lemma eq_bot_of_forall_not_mem (K : SimplicialComplex 𝕜 E) (h : ∀ s, s ∉ K) : K = ⊥ := by
  ext s; exact iff_of_false (h s) id

@[simp]
lemma space_eq_empty : K.space = ∅ ↔ K = ⊥ := by
  simp only [Set.eq_empty_iff_forall_not_mem, mem_space_iff, SimplicialComplex.ext_iff,
    @forall_swap E, mem_faces_iff, exists_prop, not_exists, not_and, faces_bot]
  simp only [← Set.eq_empty_iff_forall_not_mem, convexHull_empty_iff, coe_eq_empty]
  exact forall₂_congr fun s hs ↦ iff_false_intro (K.nonempty hs).ne_empty

@[simp]
lemma space_nonempty : K.space.Nonempty ↔ K ≠ ⊥ :=
  Set.nonempty_iff_ne_empty.trans space_eq_empty.not

@[simp, norm_cast]
lemma coe_eq_empty : (K : Set (Finset E)) = ∅ ↔ K = ⊥ := by
  simp [Set.eq_empty_iff_forall_not_mem, SimplicialComplex.ext_iff]

@[simp, norm_cast]
lemma coe_nonempty : (K : Set (Finset E)).Nonempty ↔ K ≠ ⊥ :=
  Set.nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp] lemma faces_eq_coe : K.faces = K := rfl

lemma facets_singleton (hK : K.faces = {s}) : K.facets = {s} := by
  rw [Set.eq_singleton_iff_unique_mem] at hK ⊢
  exact ⟨⟨hK.1, fun t ht _ => (hK.2 _ ht).symm⟩, fun t ht => hK.2 _ ht.1⟩

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps]
def ofSubcomplex' (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces ⊆ K.faces)
    (down_closed : ∀ ⦃s t : Finset E⦄, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces) :
    SimplicialComplex 𝕜 E where
  faces := faces
  not_empty_mem h := K.not_empty_mem (subset h)
  indep hs := K.indep (subset hs)
  down_closed hs hts ht := down_closed hs hts <| nonempty_iff_ne_empty.2 ht
  inter_subset_convexHull hs ht := K.inter_subset_convexHull (subset hs) (subset ht)

lemma ofSubcomplex_le (K : SimplicialComplex 𝕜 E) (faces) {subset down_closed} :
    K.ofSubcomplex' faces subset down_closed ≤ K := subset

lemma ofSubcomplex_bot (faces) {subset down_closed} :
    (⊥ : SimplicialComplex 𝕜 E).ofSubcomplex' faces subset down_closed = ⊥ :=
  le_bot_iff.1 <| ofSubcomplex_le _ _

lemma mem_of_mem_convexHull (hx : x ∈ K.vertices) (hs : s ∈ K)
    (hxs : x ∈ convexHull 𝕜 (s : Set E)) : x ∈ s := by
  have h := K.inter_subset_convexHull hx hs ⟨by simp, hxs⟩
  by_contra H
  rwa [←coe_inter, inter_comm, disjoint_iff_inter_eq_empty.1 (disjoint_singleton_right.2 H),
    coe_empty, convexHull_empty] at h

lemma subset_of_convexHull_subset_convexHull (hs : s ∈ K) (ht : t ∈ K)
    (hst : convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t) : s ⊆ t := fun _x hxs =>
  mem_of_mem_convexHull (K.down_closed' hs (singleton_subset_iff.2 hxs) <| singleton_nonempty _)
      ht <| hst <| subset_convexHull 𝕜 (↑s) hxs

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {K : SimplicialComplex 𝕜 E} {x y : E}
  {s t : Finset E} {A : Set (Finset E)} {m n : ℕ}

/-- A constructor for simplicial complexes by specifying a set of faces to close downward. -/
@[simps]
def ofSetClosure (indep : ∀ {s : Finset E}, s ∈ A → AffineIndependent 𝕜 ((↑) : s → E))
    (inter_subset_convexHull :
      ∀ {s t}, s ∈ A → t ∈ A → convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)) :
    SimplicialComplex 𝕜 E where
  faces := {s | s.Nonempty ∧ ∃ t, t ∈ A ∧ s ⊆ t}
  indep := fun ⟨hs, t, ht, hst⟩ => (indep ht).mono hst
  down_closed := fun ⟨hs, u, hu, hsu⟩ hts ht =>
    ⟨nonempty_iff_ne_empty.2 ht, u, hu, hts.trans hsu⟩
  inter_subset_convexHull := sorry
    -- rintro v s ⟨hv, t, ht, hvt⟩ ⟨hs, u, hu, hsu⟩ x ⟨hxv, hxs⟩
    -- have hxtu : x ∈ convexHull 𝕜 (t ∩ u : Set E) :=
    --   inter_subset_convexHull ht hu ⟨convexHull_mono hvt hxv, convexHull_mono hsu hxs⟩
    -- have hxvu : x ∈ convexHull 𝕜 (v ∩ u : Set E) := by
    --   have := AffineIndependent.subset_convexHull_inter (indep ht) hvt (inter_subset_left t u)
    --   norm_cast at this hxtu
    --   exact_mod_cast
    --     convexHull_mono (inter_subset_inter_left <| inter_subset_right t u) (this ⟨hxv, hxtu⟩)
    -- have hxts : x ∈ convexHull 𝕜 (t ∩ s : Set E) := by
    --   have := AffineIndependent.subset_convexHull_inter (indep hu) (inter_subset_right t u) hsu
    --   norm_cast at this hxtu
    --   exact_mod_cast
    --     convexHull_mono (inter_subset_inter_right <| inter_subset_left t u) (this ⟨hxtu, hxs⟩)
    -- norm_cast at hxvu hxts
    -- have hxvs :=
    --   AffineIndependent.subset_convexHull_inter (indep ht)
    --     ((inter_subset_inter_right hvt).trans <| inter_subset_left t u) (inter_subset_left t s)
    --     ⟨hxvu, hxts⟩
    -- norm_cast at hxvs
    -- exact_mod_cast convexHull_mono ((inter_subset_inter_right <| inter_subset_left v u).trans <|
    --   inter_subset_inter_left <| inter_subset_right t s)hxvs
  not_empty_mem h := h.1.ne_empty rfl

/-- A constructor for simplicial complexes by specifying a face to close downward. -/
@[simp]
def ofSimplex (indep : AffineIndependent 𝕜 ((↑) : s → E)) : SimplicialComplex 𝕜 E :=
  ofSetClosure (by rintro t (ht : t = s); rw [ht]; exact indep)
    (by rintro t u (ht : t = s) (hu : u = s); rw [ht, hu, Set.inter_self _, Set.inter_self _])

lemma mem_ofSimplex (hs : AffineIndependent 𝕜 ((↑) : s → E)) :
    t ∈ ofSimplex hs ↔ t.Nonempty ∧ t ⊆ s := by
  refine' ⟨_, fun h => ⟨h.1, s, rfl, h.2⟩⟩
  rintro ⟨ht, u, rfl : u = s, hts⟩
  exact ⟨ht, hts⟩

-- Corollary of `affine_independent.card_le_finrank_succ`
lemma face_dimension_le_space_dimension [FiniteDimensional 𝕜 E] (hs : s ∈ K) :
    s.card ≤ FiniteDimensional.finrank 𝕜 E + 1 := by
  simpa using (K.indep hs).card_le_finrank_succ.trans (add_le_add_right (Submodule.finrank_le _) _)

lemma subfacet [FiniteDimensional 𝕜 E] (hs : s ∈ K) : ∃ t, t ∈ K.facets ∧ s ⊆ t := by
  have := id hs
  revert this
  refine strongDownwardInductionOn s ?_ (face_dimension_le_space_dimension hs)
  rintro t h - ht
  by_cases htfacet : t ∈ K.facets
  · exact ⟨t, htfacet, Subset.rfl⟩
  obtain ⟨u, hu, htu⟩ := (not_facet_iff_subface ht).mp htfacet
  obtain ⟨v, hv⟩ := h (face_dimension_le_space_dimension hu) htu hu
  exact ⟨v, hv.1, htu.1.trans hv.2⟩

lemma facets_eq_empty_iff [FiniteDimensional 𝕜 E] : K.facets = ∅ ↔ K = ⊥ := by
  refine' ⟨fun h => _, _⟩
  · ext s
    refine' iff_of_false (fun hs => _) (Set.not_mem_empty _)
    obtain ⟨t, ht, -⟩ := subfacet hs
    exact h.subset ht
  · rintro rfl
    exact facets_bot

end LinearOrderedField

end Geometry.SimplicialComplex
