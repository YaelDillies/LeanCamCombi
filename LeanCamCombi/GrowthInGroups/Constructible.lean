/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import LeanCamCombi.GrowthInGroups.SubbooleanAlgebra

/-!
# Constructible sets
-/

open Set

variable {α : Type*} [TopologicalSpace α] {s t : Set α} {a : α}

/-! ### Retrocompact sets -/

def IsRetrocompact (s : Set α) : Prop := ∀ ⦃U⦄, IsCompact U → IsOpen U → IsCompact (s ∩ U)

@[simp] lemma IsRetrocompact.empty : IsRetrocompact (∅ : Set α) := by simp [IsRetrocompact]

@[simp] lemma IsRetrocompact.singleton : IsRetrocompact {a} :=
  fun _ _ _ ↦ Subsingleton.singleton_inter.isCompact

lemma IsRetrocompact.union (hs : IsRetrocompact s) (ht : IsRetrocompact t) :
    IsRetrocompact (s ∪ t : Set α) :=
  fun _U hUcomp hUopen ↦ union_inter_distrib_right .. ▸ (hs hUcomp hUopen).union (ht hUcomp hUopen)

lemma IsRetrocompact.inter [T2Space α] (hs : IsRetrocompact s) (ht : IsRetrocompact t) :
    IsRetrocompact (s ∩ t : Set α) :=
  fun _U hUcomp hUopen ↦ inter_inter_distrib_right .. ▸ (hs hUcomp hUopen).inter (ht hUcomp hUopen)

lemma IsRetrocompact.inter_isOpen (hs : IsRetrocompact s) (ht : IsRetrocompact t)
    (htopen : IsOpen t) : IsRetrocompact (s ∩ t : Set α) :=
  fun _U hUcomp hUopen ↦ inter_assoc .. ▸ hs (ht hUcomp hUopen) (htopen.inter hUopen)

lemma IsRetrocompact.isOpen_inter (hs : IsRetrocompact s) (ht : IsRetrocompact t)
    (hsopen : IsOpen s) : IsRetrocompact (s ∩ t : Set α) :=
  inter_comm .. ▸ ht.inter_isOpen hs hsopen

def IsConstructible (s : Set α) : Prop :=
  ∃ F : Set (Set α × Set α), F.Finite ∧ ⋃ UV ∈ F, UV.1 \ UV.2 = s ∧
    ∀ UV ∈ F, IsOpen UV.1 ∧ IsOpen UV.2 ∧ IsRetrocompact UV.1 ∧ IsRetrocompact UV.2

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
    ∀ UV ∈ F, IsOpen UV.1 ∧ IsOpen UV.2 ∧ IsRetrocompact UV.1 ∧ IsRetrocompact UV.2
