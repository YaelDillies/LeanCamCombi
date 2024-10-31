/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import LeanCamCombi.GrowthInGroups.BooleanSubalgebra

/-!
# Constructible sets
-/

open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s t : Set α} (f : α → β) {a : α}

/-! ### Retrocompact sets -/

def IsRetroCompact (s : Set α) : Prop := ∀ ⦃U⦄, IsCompact U → IsOpen U → IsCompact (s ∩ U)

@[simp] lemma IsRetroCompact.empty : IsRetroCompact (∅ : Set α) := by simp [IsRetroCompact]

@[simp] lemma IsRetroCompact.singleton : IsRetroCompact {a} :=
  fun _ _ _ ↦ Subsingleton.singleton_inter.isCompact

lemma IsRetroCompact.union (hs : IsRetroCompact s) (ht : IsRetroCompact t) :
    IsRetroCompact (s ∪ t : Set α) :=
  fun _U hUcomp hUopen ↦ union_inter_distrib_right .. ▸ (hs hUcomp hUopen).union (ht hUcomp hUopen)

lemma IsRetroCompact.inter [T2Space α] (hs : IsRetroCompact s) (ht : IsRetroCompact t) :
    IsRetroCompact (s ∩ t : Set α) :=
  fun _U hUcomp hUopen ↦ inter_inter_distrib_right .. ▸ (hs hUcomp hUopen).inter (ht hUcomp hUopen)

lemma IsRetroCompact.inter_isOpen (hs : IsRetroCompact s) (ht : IsRetroCompact t)
    (htopen : IsOpen t) : IsRetroCompact (s ∩ t : Set α) :=
  fun _U hUcomp hUopen ↦ inter_assoc .. ▸ hs (ht hUcomp hUopen) (htopen.inter hUopen)

lemma IsRetroCompact.isOpen_inter (hs : IsRetroCompact s) (ht : IsRetroCompact t)
    (hsopen : IsOpen s) : IsRetroCompact (s ∩ t : Set α) :=
  inter_comm .. ▸ ht.inter_isOpen hs hsopen

def IsConstructible (s : Set α) : Prop :=
  ∃ F : Set (Set α × Set α), F.Finite ∧ ⋃ UV ∈ F, UV.1 \ UV.2 = s ∧
    ∀ UV ∈ F, IsOpen UV.1 ∧ IsOpen UV.2 ∧ IsRetroCompact UV.1 ∧ IsRetroCompact UV.2

@[simp] lemma IsConstructible.empty : IsConstructible (∅ : Set α) := ⟨∅, by simp⟩

lemma IsConstructible.iUnion {ι : Sort*} [Finite ι] {f : ι → Set α}
    (hf : ∀ i, IsConstructible (f i)) : IsConstructible (⋃ i, f i) := by
  choose F hFfin hFS hF using hf
  exact ⟨⋃ i, F i, finite_iUnion hFfin, by simp [iUnion_comm, hFS],
    by simpa [forall_swap (α := ι)] using hF⟩

lemma IsConstructible.sUnion {S : Set (Set α)} (hSfin : S.Finite)
    (hS : ∀ s ∈ S, IsConstructible s) : IsConstructible (⋃₀ S) := by
  have := hSfin.to_subtype; exact sUnion_eq_iUnion ▸ .iUnion (by simpa)

lemma IsConstructible.union (hs : IsConstructible s) (ht : IsConstructible t) :
    IsConstructible (s ∪ t) := by
  rw [← sUnion_pair]; exact .sUnion (toFinite _) (by simpa using And.intro hs ht)

@[simp] lemma IsConstructible.compl (hs : IsConstructible s) : IsConstructible sᶜ := by
  sorry
  -- obtain ⟨F, hFfin, rfl, hF⟩ := hs
  -- exact ⟨.swap '' F, hFfin.image _, _⟩


def IsLocallyConstructible (s : Set α) : Prop :=
  ∃ F : Set (Set α × Set α), F.Finite ∧ ⋃ UV ∈ F, UV.1 \ UV.2 = s ∧
    ∀ UV ∈ F, IsOpen UV.1 ∧ IsOpen UV.2 ∧ IsRetroCompact UV.1 ∧ IsRetroCompact UV.2

lemma IsRetroCompact.isCompact [CompactSpace α] {s : Set α} (hs : IsRetroCompact s) :
    IsCompact s := by
  simpa using hs CompactSpace.isCompact_univ

lemma IsRetroCompact.isConstructible {s : Set α} (hs : IsRetroCompact s)
    (hs' : IsOpen s) : IsConstructible s := sorry


@[stacks 09YD]
lemma IsConstructible.image_of_isOpenEmbedding {s : Set α} (hs : IsConstructible s)
    (hf : IsOpenEmbedding f) (hf' : IsRetroCompact (Set.range f)) : IsConstructible (f '' s) :=
  sorry

@[stacks 005J]
lemma IsConstructible.preimage_of_isOpenEmbedding {s : Set β} (hs : IsConstructible s)
    (hf : IsOpenEmbedding f) : IsConstructible (f ⁻¹' s) :=
  sorry

@[stacks 09YG]
lemma IsConstructible.image_of_isClosedEmbedding {s : Set α} (hs : IsConstructible s)
    (hf : IsClosedEmbedding f) (hf' : IsRetroCompact (Set.range f)ᶜ) : IsConstructible (f '' s) :=
  sorry

@[stacks 09YE]
lemma IsConstructible.preimage_of_isClosedEmbedding {s : Set β} (hs : IsConstructible s)
    (hf : IsClosedEmbedding f) (hf' : IsCompact (Set.range f)ᶜ) : IsConstructible (f ⁻¹' s) :=
  sorry

variable {ι} (b : ι → Set α) (hb : TopologicalSpace.IsTopologicalBasis (Set.range b))

include hb in
lemma isRetroCompact_iff_isCompact_of_isTopologicalBasis [CompactSpace α]
    (hb' : ∀ i j, IsCompact (b i ∩ b j))
    {U : Set α} (hU : IsOpen U) :
    IsRetroCompact U ↔ IsCompact U := by
  refine ⟨IsRetroCompact.isCompact, fun hU' {V} hV' hV ↦ ?_⟩
  have hb'' : ∀ i, IsCompact (b i) := fun i ↦ by simpa using hb' i i
  obtain ⟨s, hs, rfl⟩ :=
    (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b hb hb'' U).mp ⟨hU', hU⟩
  obtain ⟨t, ht, rfl⟩ :=
    (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b hb hb'' V).mp ⟨hV', hV⟩
  simp only [Set.iUnion_inter, Set.inter_iUnion]
  exact ht.isCompact_biUnion fun _ _ ↦ hs.isCompact_biUnion fun _ _ ↦ (hb' _ _)

include hb in
lemma IsConstructible.induction_of_isTopologicalBasis
    (P : Set α → Prop)
    (hP : ∀ i s, Set.Finite s → P (b i \ ⋃ j ∈ s, b j))
    (hP' : ∀ s t, P s → P t → P (s ∪ t))
    (s : Set α) (hs : IsConstructible s) : P s := sorry
