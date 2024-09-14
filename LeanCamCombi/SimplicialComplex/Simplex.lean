/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.LinearAlgebra.FiniteDimensional
import LeanCamCombi.Mathlib.Analysis.Convex.Extreme

/-!
# Definitions and lemmas about individual simplices

These are phrased in terms of finite sets of points, and the assumption of affine independence
(ie non-degeneracy) is added to lemmas.
-/

open Set
open scoped BigOperators Classical

variable {𝕜 E ι : Type*}

section OrderedRing
variable (𝕜) [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Finset E} {x : E}

/-- The combinatorial frontier of a simplex as a subspace. -/
def combiFrontier (s : Finset E) : Set E := ⋃ (t) (_ : t ⊂ s), convexHull 𝕜 ↑t

/-- The interior of a simplex as a subspace. Note this is *not* the same thing as the topological
interior of the underlying space. -/
def combiInterior (s : Finset E) : Set E := convexHull 𝕜 ↑s \ combiFrontier 𝕜 s

variable {𝕜}

lemma mem_combiFrontier_iff :
    x ∈ combiFrontier 𝕜 s ↔ ∃ t, t ⊂ s ∧ x ∈ convexHull 𝕜 (t : Set E) := by simp [combiFrontier]

lemma combiFrontier_subset_convexHull : combiFrontier 𝕜 s ⊆ convexHull 𝕜 ↑s :=
  iUnion₂_subset fun _t ht => convexHull_mono ht.1

lemma combiInterior_subset_convexHull : combiInterior 𝕜 s ⊆ convexHull 𝕜 ↑s := diff_subset

@[simp] lemma combiFrontier_empty : combiFrontier 𝕜 (∅ : Finset E) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  convert combiFrontier_subset_convexHull
  rw [Finset.coe_empty, convexHull_empty]

@[simp] lemma combiInterior_empty : combiInterior 𝕜 (∅ : Finset E) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  convert combiInterior_subset_convexHull
  rw [Finset.coe_empty, convexHull_empty]

@[simp] lemma combiFrontier_singleton : combiFrontier 𝕜 ({x} : Finset E) = ∅ := by
  refine eq_empty_of_subset_empty fun y hy ↦ ?_
  rw [mem_combiFrontier_iff] at hy
  obtain ⟨s, hs, hys⟩ := hy
  rw [Finset.eq_empty_of_ssubset_singleton hs] at hys
  simp at hys

@[simp] lemma combiInterior_singleton : combiInterior 𝕜 ({x} : Finset E) = {x} := by
  unfold combiInterior
  rw [combiFrontier_singleton]
  simp

lemma convexHull_eq_interior_union_combiFrontier :
    convexHull 𝕜 ↑s = combiInterior 𝕜 s ∪ combiFrontier 𝕜 s :=
  (diff_union_of_subset combiFrontier_subset_convexHull).symm

lemma simplex_combiInteriors_cover : convexHull 𝕜 ↑s = ⋃ (t) (_ : t ⊆ s), combiInterior 𝕜 t := by
  apply Subset.antisymm _ _
  · refine s.strongInductionOn ?_
    rintro s ih x hx
    by_cases h : x ∈ combiFrontier 𝕜 s
    · rw [mem_combiFrontier_iff] at h
      obtain ⟨t, st, ht⟩ := h
      specialize ih _ st ht
      simp only [exists_prop, Set.mem_iUnion] at ih ⊢
      obtain ⟨Z, Zt, hZ⟩ := ih
      exact ⟨_, Zt.trans st.1, hZ⟩
    · exact subset_iUnion₂ s Subset.rfl ⟨hx, h⟩
  · exact iUnion₂_subset fun t ht ↦ diff_subset.trans $ convexHull_mono ht

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Finset E} {x : E}

lemma combiFrontier_eq :
    combiFrontier 𝕜 s = {x : E | ∃ (w : E → 𝕜)
      (_hw₀ : ∀ y ∈ s, 0 ≤ w y) (_hw₁ : ∑ y in s, w y = 1) (_hw₂ : ∃ y ∈ s, w y = 0),
        s.centerMass w id = x} := by
  ext x
  simp_rw [combiFrontier, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · simp only [and_imp, exists_prop, exists_imp]
    intro t ts hx
    rw [Finset.convexHull_eq, Set.mem_setOf_eq] at hx
    rcases hx with ⟨w, hw₀, hw₁, hx⟩
    rcases Finset.exists_of_ssubset ts with ⟨y, hys, hyt⟩
    let w' z := if z ∈ t then w z else 0
    have hw'₁ : s.sum w' = 1 := by
      rwa [← Finset.sum_subset ts.1, Finset.sum_extend_by_zero]
      simp only [ite_eq_right_iff]
      tauto
    refine ⟨w', ?_, hw'₁, ⟨_, ‹y ∈ s›, ?_⟩, ?_⟩
    · rintro y -
      change 0 ≤ ite (y ∈ t) (w y) 0
      split_ifs
      · apply hw₀ y ‹_›
      · rfl
    · apply if_neg ‹y ∉ t›
    rw [← Finset.centerMass_subset id ts.1]
    · rw [Finset.centerMass_eq_of_sum_1]
      · rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁] at hx
        rw [← hx]
        apply Finset.sum_congr rfl
        intro x hx
        change ite _ _ _ • _ = _
        rw [if_pos hx]
      rwa [Finset.sum_extend_by_zero]
    exact fun i _ hi => if_neg hi
  · simp only [and_imp, exists_prop, exists_imp]
    intro w hw₁ hw₂ y hy₁ hy₂ hy₃
    refine ⟨s.erase y, Finset.erase_ssubset hy₁, ?_⟩
    rw [Finset.convexHull_eq, Set.mem_setOf_eq]
    refine ⟨w, fun z hz => hw₁ z (s.erase_subset _ hz), ?_, ?_⟩
    rw [Finset.sum_erase _ hy₂]
    apply hw₂
    rwa [Finset.centerMass_subset _ (s.erase_subset _)]
    intro i hi₁ hi₂
    simp only [hi₁, and_true, Classical.not_not, Finset.mem_erase] at hi₂
    subst hi₂
    apply hy₂

lemma combiInterior_subset_positive_weighings :
    combiInterior 𝕜 s ⊆
      {x : E | ∃ (w : E → 𝕜)
        (_hw₀ : ∀ y ∈ s, 0 < w y) (_hw₁ : ∑ y in s, w y = 1), s.centerMass w id = x} := by
  rw [combiInterior, Finset.convexHull_eq, combiFrontier_eq]
  rintro x
  simp only [not_exists, and_imp, not_and, mem_setOf_eq, mem_diff, exists_imp]
  rintro w hw₁ hw₂ hw₃ q
  refine ⟨w, fun y hy => ?_, hw₂, hw₃⟩
  exact lt_of_le_of_ne (hw₁ _ hy) (Ne.symm fun t => q w hw₁ hw₂ y hy t hw₃)

lemma combiInterior_eq (hs : AffineIndependent 𝕜 ((↑) : s → E)) :
    combiInterior 𝕜 s = {x : E | ∃ (w : E → 𝕜)
      (_hw₀ : ∀ y ∈ s, 0 < w y) (_hw₁ : ∑ y in s, w y = 1), s.centerMass w id = x} := by
  refine combiInterior_subset_positive_weighings.antisymm fun x => ?_
  rw [combiInterior, Finset.convexHull_eq, combiFrontier_eq]
  simp only [not_exists, and_imp, not_and, mem_setOf_eq, mem_diff, exists_imp]
  intro w hw₀ hw₁ hw₂
  refine ⟨⟨w, fun y hy => (hw₀ y hy).le, hw₁, hw₂⟩, fun v hv₀ hv₁ y hy hvy hv₂ => (hw₀ y hy).ne' ?_⟩
  rw [← hv₂] at hw₂
  rw [Finset.centerMass_eq_of_sum_1 _ _ hv₁, Finset.centerMass_eq_of_sum_1 _ _ hw₁] at hw₂
  rw [← hvy]
  exact hs.eq_of_sum_eq_sum_subtype (hw₁.trans hv₁.symm) hw₂ _ hy

lemma centroid_mem_combiInterior (hs : AffineIndependent 𝕜 ((↑) : s → E)) (hs' : s.Nonempty) :
    s.centroid 𝕜 id ∈ combiInterior 𝕜 s := by
  rw [Finset.centroid_def]
  have hsweights := s.sum_centroidWeights_eq_one_of_nonempty 𝕜 hs'
  rw [affineCombination_eq_centerMass hsweights]
  rw [combiInterior_eq hs]
  refine ⟨_, fun y _ => ?_, hsweights, rfl⟩
  simpa using hs'.card_pos

protected lemma Finset.Nonempty.combiInterior (hs : AffineIndependent 𝕜 ((↑) : s → E))
    (hsnonempty : s.Nonempty) : (combiInterior 𝕜 s).Nonempty :=
  ⟨s.centroid 𝕜 id, centroid_mem_combiInterior hs hsnonempty⟩

lemma combiInterior.inj (hs : AffineIndependent 𝕜 ((↑) : s → E))
    (ht : AffineIndependent 𝕜 ((↑) : t → E)) (h : combiInterior 𝕜 s = combiInterior 𝕜 t) :
    s = t :=
  sorry

lemma convex_combiInterior (hs : AffineIndependent 𝕜 ((↑) : s → E)) :
    Convex 𝕜 (combiInterior 𝕜 s) := by
  simp_rw [convex_iff_forall_pos, combiInterior_eq hs]
  rintro x ⟨v, hv₀, hv₁, rfl⟩ y ⟨w, hw₀, hw₁, rfl⟩ a b ha hb h
  refine ⟨fun x => a * v x + b * w x, fun x hx => ?_, ?_, ?_⟩
  · exact add_pos (mul_pos ha <| hv₀ x hx) (mul_pos hb <| hw₀ x hx)
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hv₁, hw₁]
    simp [h]
  rw [Finset.centerMass_segment _ _ _ _ hv₁ hw₁ _ _ h]

end LinearOrderedField

section Real
section TopologicalSpace
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] {s t : Finset E}

lemma Finset.isClosed_convexHull (s : Finset E) : IsClosed (convexHull ℝ (s : Set E)) :=
  s.finite_toSet.isClosed_convexHull

lemma isClosed_combiFrontier : IsClosed (combiFrontier ℝ s) := by
  refine Set.Finite.isClosed_biUnion ?_ fun t _ => t.isClosed_convexHull
  suffices Set.Finite {t | t ⊆ s} by exact this.subset fun i h => h.1
  convert s.powerset.finite_toSet using 1
  ext
  simp

/-- `combiInterior 𝕜 s` is the topological interior iff `s` is of dimension `m`. -/
lemma interiors_agree_of_full_dimensional [FiniteDimensional ℝ E]
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hscard : s.card = FiniteDimensional.finrank ℝ E + 1) :
    combiInterior ℝ s = interior (convexHull ℝ ↑s) := by
  unfold combiInterior
  sorry

lemma frontiers_agree_of_full_dimensional [FiniteDimensional ℝ E]
    (hscard : s.card = FiniteDimensional.finrank ℝ E + 1) :
    combiFrontier ℝ s = frontier (convexHull ℝ ↑s) := by
  ext x
  constructor
  · unfold combiFrontier
    simp_rw [Set.mem_iUnion]
    rintro ⟨t, hts, hx⟩
    constructor
    · exact subset_closure (convexHull_mono hts.1 hx)
    · rintro h
      sorry
  --have :=  finset.convexHull_eq,
  · rintro ⟨h, g⟩
    sorry

end TopologicalSpace

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s t : Finset E}

lemma subset_closure_combiInterior (hs : AffineIndependent ℝ ((↑) : s → E)) :
    (s : Set E) ⊆ closure (combiInterior ℝ s) := by
  rintro x (hx : x ∈ s)
  apply seqClosure_subset_closure
  have hsnonempty : s.Nonempty := ⟨x, hx⟩
  have centroid_weights : ∑ i : E in s, Finset.centroidWeights ℝ s i = 1 := by
    apply Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ hsnonempty
  refine ⟨fun n => ?_, fun n => ?_, ?_⟩
  · apply ((n : ℝ) + 2)⁻¹ • s.centroid ℝ id + (1 - ((n : ℝ) + 2)⁻¹) • x
  · rw [Finset.centroid_def]
    rw [affineCombination_eq_centerMass _]
    · rw [← id_def x]
      rw [← Finset.centerMass_ite_eq (R := ℝ) _ _ id hx]
      simp only
      rw [Finset.centerMass_segment]
      · rw [combiInterior_eq hs]
        refine ⟨_, ?_, ?_, rfl⟩
        · simp only [mul_boole, Finset.centroidWeights_apply]
          intro y hy
          apply add_pos_of_pos_of_nonneg
          · apply mul_pos
            · rw [inv_pos]
              norm_cast
              simp
            · rw [inv_pos]
              norm_cast
              rwa [Finset.card_pos]
          · split_ifs
            · rw [sub_nonneg]
              apply inv_le_one
              norm_cast
              apply Nat.succ_pos
            · rfl
        sorry
        -- broken because of non-canonical instance
        -- rw [Finset.sum_add_distrib, ← Finset.mul_sum, centroid_weights, ← Finset.mul_sum,
        --   Finset.sum_boole, Finset.filter_eq]
        -- simp [hx]
      · apply centroid_weights
      · simp [Finset.sum_boole, Finset.filter_eq, hx]
      · simp only [add_sub_cancel]
    apply Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ hsnonempty
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    convert_to Filter.Tendsto (fun e : ℕ => ((e : ℝ) + 2)⁻¹ * ‖s.centroid ℝ id - x‖) Filter.atTop _
    · ext n
      rw [add_sub_assoc, sub_smul, sub_right_comm, one_smul, sub_self, zero_sub, ← smul_neg, ←
        smul_add, norm_smul_of_nonneg, ← sub_eq_add_neg]
      rw [inv_nonneg]
      norm_cast
      apply Nat.zero_le
    suffices Filter.Tendsto (fun e : ℕ => (↑(e + 2) : ℝ)⁻¹) Filter.atTop (nhds 0) by
      simpa using this.mul_const _
    refine tendsto_inv_atTop_zero.comp ?_
    rw [tendsto_natCast_atTop_iff]
    apply Filter.tendsto_add_atTop_nat

variable [T2Space E]

-- Affine indep is necessary, since if not combiInterior can be empty
lemma closure_combiInterior_eq_convexHull (hs : AffineIndependent ℝ ((↑) : s → E)) :
    closure (combiInterior ℝ s) = convexHull ℝ (s : Set E) := by
  refine Set.Subset.antisymm ?_
    (convexHull_min (subset_closure_combiInterior hs) (convex_combiInterior hs).closure)
  rw [s.isClosed_convexHull.closure_subset_iff]
  exact combiInterior_subset_convexHull

lemma convexHull_subset_convexHull_of_combiInterior_subset_combiInterior
    (hs : AffineIndependent ℝ ((↑) : s → E)) (ht : AffineIndependent ℝ ((↑) : t → E)) :
    combiInterior ℝ s ⊆ combiInterior ℝ t →
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  rw [← closure_combiInterior_eq_convexHull hs]
  rw [← closure_combiInterior_eq_convexHull ht]
  intro h
  apply closure_mono h

end SeminormedAddCommGroup

end Real
