/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import LeanCamCombi.SimplicialComplex.Basic

/-!
# Finite simplicial complexes
-/

open Set

variable {𝕜 E ι : Type*}

namespace Geometry.SimplicialComplex
variable [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {K K₁ K₂ : SimplicialComplex 𝕜 E} {x t : E}
  {s t : Finset E} {A : Set (Finset E)} {m n : ℕ}

/-- A simplicial complex is finite iff it has finitely many faces. -/
protected def Finite (K : SimplicialComplex 𝕜 E) : Prop := K.faces.Finite

noncomputable def facesFinset (K : SimplicialComplex 𝕜 E) (hS : K.Finite) : Finset (Finset E) :=
  hS.toFinset

@[simp]
lemma mem_facesFinset (hS : K.Finite) : s ∈ K.facesFinset hS ↔ s ∈ K.faces :=
  Set.Finite.mem_toFinset _

/-- A simplicial complex `S` is locally finite at the face `s` iff `s` is a subface of finitely many
faces in `S`. -/
def LocallyFiniteAt (K : SimplicialComplex 𝕜 E) (s : Finset E) : Prop :=
  {t ∈ K.faces | s ⊆ t}.Finite

/-- A simplicial complex `S` is locally finite at the face `s` iff `s` is a subface of infinitely
many faces in `S`. -/
def LocallyInfiniteAt (K : SimplicialComplex 𝕜 E) (s : Finset E) : Prop :=
  {t ∈ K.faces | s ⊆ t}.Infinite

@[simp] lemma not_locallyInfiniteAt_iff : ¬K.LocallyInfiniteAt s ↔ K.LocallyFiniteAt s := not_not

/-- A simplicial complex is locally finite iff each of its nonempty faces belongs to finitely many
faces. -/
def LocallyFinite (K : SimplicialComplex 𝕜 E) : Prop :=
  ∀ ⦃s : Finset _⦄, s ∈ K.faces → s.Nonempty → K.LocallyFiniteAt s

lemma LocallyFiniteAt.mono (hX : K.LocallyFiniteAt s) (hXY : s ⊆ t) : K.LocallyFiniteAt t := by
  apply hX.subset
  rintro u ⟨_, _⟩
  exact ⟨‹u ∈ K.faces›, hXY.trans ‹t ⊆ u›⟩

lemma LocallyInfiniteAt.mono (hXY : s ⊆ t) (hY : K.LocallyInfiniteAt t) : K.LocallyInfiniteAt s :=
  fun t => hY <| LocallyFiniteAt.mono t hXY

protected lemma Finite.locallyFinite (hS : K.Finite) : K.LocallyFinite :=
  fun _s _hX _ => hS.subset fun _t hY => hY.1

/-- A simplicial complex is locally finite iff each point belongs to finitely many faces. -/
lemma locallyFinite_iff_mem_finitely_many_faces [DecidableEq E] :
    K.LocallyFinite ↔ ∀ x, {s | s ∈ K.faces ∧ x ∈ convexHull 𝕜 (s : Set E)}.Finite := by
  constructor
  · unfold LocallyFinite
    contrapose!
    rintro ⟨x, hx⟩
    by_cases hxspace : x ∈ K.space
    · obtain ⟨s, ⟨hX, hXhull, hXbound⟩, hXunique⟩ := combiInteriors_partition hxspace
      simp at hXunique
      refine
        ⟨s, hX, Finset.nonempty_of_ne_empty ?_, fun hXlocallyfinite =>
          hx <| hXlocallyfinite.subset fun t hY => ⟨hY.1, ?_⟩⟩
      · rintro rfl
        simp at hXhull
      have hXYhull := K.inter_subset_convexHull hX hY.1 ⟨hXhull, hY.2⟩
      rw [← Finset.coe_inter] at hXYhull
      by_contra hXY
      exact hXbound (mem_combiFrontier_iff.2 ⟨s ∩ t, ⟨Finset.inter_subset_left,
        fun hXXY => hXY (Finset.subset_inter_iff.1 hXXY).2⟩, hXYhull⟩)
    · refine (hx ?_).elim
      convert finite_empty
      exact eq_empty_of_forall_not_mem fun s hX => hxspace <| mem_biUnion hX.1 hX.2
  · rintro hS s - ⟨x, hx⟩
    exact (hS x).subset fun t => And.imp_right fun ht => subset_convexHull _ _ <| ht hx

end Geometry.SimplicialComplex
