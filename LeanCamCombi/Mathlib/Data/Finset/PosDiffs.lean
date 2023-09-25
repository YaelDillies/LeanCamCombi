/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Set.Intervals.OrdConnected
import Mathlib.Order.UpperLower.Basic
import LeanCamCombi.Mathlib.Data.Finset.Basic
import LeanCamCombi.Mathlib.Data.Finset.Sups

/-!
# Positive difference

This file defines the positive difference of set families and sets in an ordered additive group.

## Main declarations

* `Finset.posDiffs`: Positive difference of set families.
* `Finset.posSub`: Positive difference of sets in an ordered additive group.

## Notations

We declare the following notation in the `finset_family` locale:
* `s \₊ t` for `finset.posDiffs s t`
* `s -₊ t` for `finset.posSub s t`

## References

* [Bollobás, Leader, Radcliffe, *Reverse Kleitman Inequalities][bollobasleaderradcliffe1989]
-/

open scoped Pointwise

variable {α : Type*}
namespace Finset

@[elab_as_elim]
protected theorem family_induction_on {p : Finset (Finset α) → Prop} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (h₀ : p ∅)
    (h₁ : ∀ ⦃a : α⦄ ⦃𝒜 : Finset (Finset α)⦄, (∀ s ∈ 𝒜, a ∉ s) → p 𝒜 → p (𝒜.image $ insert a))
    (h₂ :
      ∀ ⦃a : α⦄ ⦃𝒜 : Finset (Finset α)⦄,
        p (𝒜.filter ((· ∉ ·) a)) → p (𝒜.filter ((· ∈ ·) a)) → p 𝒜) :
    p 𝒜 :=
  sorry

end Finset

namespace Finset

/-! ### Positive set difference -/

section posDiffs
section GeneralizedBooleanAlgebra
variable [GeneralizedBooleanAlgebra α] [@DecidableRel α (· ≤ ·)] [DecidableEq α] {s t : Finset α}
  {a : α}

/-- The positive set difference of finsets `s` and `t` is the set of `a \ b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posDiffs (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun x ↦ x.2 ≤ x.1).image fun x ↦ x.1 \ x.2

scoped[FinsetFamily] infixl:70 " \\₊ " => Finset.posDiffs

open scoped FinsetFamily

@[simp] lemma mem_posDiffs : a ∈ s \₊ t ↔ ∃ b ∈ s, ∃ c ∈ t, c ≤ b ∧ b \ c = a := by
  simp_rw [posDiffs, mem_image, mem_filter, mem_product, Prod.exists, and_assoc, exists_and_left]

@[simp] lemma posDiffs_empty (s : Finset α) : s \₊ ∅ = ∅ := by simp [posDiffs]
@[simp] lemma empty_posDiffs (s : Finset α) : ∅ \₊ s = ∅ := by simp [posDiffs]

lemma posDiffs_subset_diffs : s \₊ t ⊆ s \\ t := by
  simp only [subset_iff, mem_posDiffs, mem_diffs]
  exact λ a ⟨b, hb, c, hc, _, ha⟩ ↦ ⟨b, hb, c, hc, ha⟩

end GeneralizedBooleanAlgebra

open scoped FinsetFamily

section Finset

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}

lemma card_posDiffs_self_le (h𝒜 : (𝒜 : Set (Finset α)).OrdConnected) :
    (𝒜 \₊ 𝒜).card ≤ 𝒜.card := by
  revert h𝒜
  refine' Finset.family_induction_on 𝒜 _ _ _
  · simp
  · rintro a 𝒜 h𝒜
    sorry
  sorry

/-- A **reverse Kleitman inequality**. -/
lemma le_card_upper_inter_lower (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) : (𝒜 \₊ ℬ).card ≤ (𝒜 ∩ ℬ).card := by
  refine' (card_le_of_subset _).trans (card_posDiffs_self_le _)
  · simp_rw [subset_iff, mem_posDiffs, mem_inter]
    rintro _ ⟨s, hs, t, ht, hts, rfl⟩
    exact ⟨s, ⟨hs, hℬ hts ht⟩, t, ⟨h𝒜 hts hs, ht⟩, hts, rfl⟩
  · rw [coe_inter]
    exact h𝒜.ordConnected.inter hℬ.ordConnected

end Finset

end posDiffs

/-! ### Positive subtraction -/


section posSub

variable [Sub α] [Preorder α] [@DecidableRel α (· ≤ ·)] [DecidableEq α] {s t : Finset α} {a : α}

/-- The positive subtraction of finsets `s` and `t` is the set of `a - b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posSub (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun x ↦ x.2 ≤ x.1).image fun x ↦ x.1 - x.2

scoped[FinsetFamily] infixl:70 " -₊ " => Finset.posSub

open scoped FinsetFamily

lemma mem_posSub : a ∈ s -₊ t ↔ ∃ b ∈ s, ∃ c ∈ t, c ≤ b ∧ b - c = a := by
  simp_rw [posSub, mem_image, mem_filter, mem_product, Prod.exists, and_assoc, exists_and_left]

lemma posSub_subset_sub : s -₊ t ⊆ s - t := fun x ↦ by
  rw [mem_posSub, mem_sub]; exact fun ⟨b, hb, c, hc, _, h⟩ ↦ ⟨b, c, hb, hc, h⟩

theorem card_posSub_self_le (hs : (s : Set α).OrdConnected) : (s -₊ s).card ≤ s.card :=
  sorry

end posSub

end Finset
