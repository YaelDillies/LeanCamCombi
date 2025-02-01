/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Partition.Finpartition
import LeanCamCombi.Mathlib.Data.Finset.Image

/-!
# Symmetric Chain Decompositions

This file shows that if `α` is finite then `Finset α` has a decomposition into symmetric chains,
namely chains of the form `{Cᵢ, ..., Cₙ₋ᵢ}` where `card α = n` and `|C_j| = j`.
-/

open Finset

namespace Finpartition
variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {𝒞 𝒟 : Finset (Finset α)}
  {C s : Finset α} {a : α}

def extendExchange (a : α) (𝒞 : Finset (Finset α)) (C : Finset α) : Finset (Finset (Finset α)) :=
  if 𝒞.Nontrivial
  then {(𝒞 \ {C}).image (insert a), 𝒞 ∪ {insert a C}}
  else {𝒞 ∪ {insert a C}}

lemma eq_or_eq_of_mem_extendExchange :
    𝒟 ∈ extendExchange a 𝒞 C → 𝒟 = (𝒞 \ {C}).image (insert a) ∨ 𝒟 = 𝒞 ∪ {insert a C} := by
  unfold extendExchange; split_ifs with h𝒞 <;> simp (config := { contextual := true })

@[simp] lemma not_empty_mem_extendExchange : ∅ ∉ extendExchange a 𝒞 C := by
  unfold extendExchange
  split_ifs with h𝒞
  · simp [eq_comm (a := ∅), ← nonempty_iff_ne_empty, h𝒞.nonempty.ne_empty, h𝒞.ne_singleton]
  · simp [eq_comm (a := ∅), ← nonempty_iff_ne_empty]

@[simp] lemma sup_extendExchange (hC : C ∈ 𝒞) :
    (extendExchange a 𝒞 C).sup id = 𝒞 ∪ 𝒞.image (insert a) := by
  unfold extendExchange
  split_ifs with h𝒞
  · simp only [sup_insert, id_eq, sup_singleton, sup_eq_union, union_left_comm]
    rw [image_sdiff_of_injOn, image_singleton, sdiff_union_of_subset]
    simpa using mem_image_of_mem _ hC
    sorry
    simpa
  · obtain rfl := (eq_singleton_or_nontrivial hC).resolve_right h𝒞
    simp

def extendPowersetExchange (P : Finpartition s.powerset) (f : ∀ 𝒞 ∈ P.parts, 𝒞) (a : α)
    (ha : a ∉ s) : Finpartition (s.cons a ha).powerset where

  -- ofErase
  --   (P.parts.attach.biUnion fun ⟨𝒞, h𝒞⟩ ↦ extendExchange a 𝒞 (f 𝒞 h𝒞).1)
  --   (by
  --     sorry
  --     )
  --   (by
  --     simp
  --     )

  parts := P.parts.attach.biUnion fun ⟨𝒞, h𝒞⟩ ↦ extendExchange a 𝒞 (f 𝒞 h𝒞).1
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.coe_biUnion, Finset.mem_coe,
      Finset.mem_attach, Set.iUnion_true, Set.mem_iUnion, Subtype.exists, ne_eq, Function.onFun,
      id_eq, forall_exists_index, not_imp_comm]
    rintro x 𝒞 h𝒞 hx y 𝒟 h𝒟 hy hxy
    obtain rfl | rfl := eq_or_eq_of_mem_extendExchange hx <;>
      obtain rfl | rfl := eq_or_eq_of_mem_extendExchange hy
    · rw [disjoint_image'] at hxy
      obtain rfl := P.disjoint.elim h𝒞 h𝒟 fun h ↦ hxy $ h.mono sdiff_le sdiff_le
      rfl
      sorry
    · sorry
    · sorry
    · simp_rw [disjoint_union_left, disjoint_union_right, and_assoc] at hxy
      obtain rfl := P.disjoint.elim h𝒞 h𝒟 fun h ↦ hxy $ ⟨h, sorry, sorry, sorry⟩
      rfl
  sup_parts := by
    ext C
    simp only [sup_biUnion, coe_mem, sup_extendExchange, mem_sup, mem_attach, mem_union, mem_image,
      true_and, Subtype.exists, exists_prop, cons_eq_insert, mem_powerset]
    constructor
    · rintro ⟨𝒞, h𝒞, hC | ⟨C, hC, rfl⟩⟩
      · exact Subset.trans (mem_powerset.1 $ P.le h𝒞 hC) (subset_insert ..)
      · exact insert_subset_insert _ (mem_powerset.1 $ P.le h𝒞 hC)
    by_cases ha : a ∈ C
    · rw [subset_insert_iff]
      rintro hC
      obtain ⟨𝒞, h𝒞, hC⟩ := P.exists_mem $ mem_powerset.2 hC
      exact ⟨𝒞, h𝒞, .inr ⟨_, hC, insert_erase ha⟩⟩
    · rw [subset_insert_iff_of_not_mem ha]
      rintro hC
      obtain ⟨𝒞, h𝒞, hC⟩ := P.exists_mem $ mem_powerset.2 hC
      exact ⟨𝒞, h𝒞, .inl hC⟩
  not_bot_mem := by simp

/-! ### Profile of a partition -/

/-- The profile of  -/
def profile (P : Finpartition s) : Multiset ℕ := P.parts.1.map card

end Finpartition
