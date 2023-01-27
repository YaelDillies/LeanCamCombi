/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import mathlib.data.finset.basic
import data.finset.sort
import data.finset.sups
import data.fintype.basic
import mathlib.order
import order.upper_lower

/-!
# Set family certificates

This file defines the certificator of two families of sets. If we consider set families `𝒜` and `ℬ`
as probabilistic events, the size of the certificator `𝒜 □ ℬ` corresponds to the probability that
`𝒜` and `ℬ` occur "disjointly".

## Main declarations

* `finset.certificator`: Certificator of two elements of a Boolean algebra
* `finset.card_certificator_le`: The Van den Berg-Kesten-Reimer inequality: The probability that `𝒜`
  and `ℬ` occur "disjointly" is less than the product of their probabilities.

## References

* D. Reimer, *Proof of the Van den Berg–Kesten Conjecture*
-/

open_locale classical finset_family

variables {α : Type*}

namespace finset
section boolean_algebra
variables [boolean_algebra α] (s t u : finset α) {a : α}

noncomputable def certificator : finset α :=
(s ∩ t).filter $ λ a, ∃ x y, is_compl x y ∧ (∀ ⦃b⦄, a ⊓ x = b ⊓ x → b ∈ s) ∧
  ∀ ⦃b⦄, a ⊓ y = b ⊓ y → b ∈ t

localized "infix (name := finset.certificator) ` □ `:70 := certificator" in finset_family

variables {s t u}

@[simp] lemma mem_certificator :
  a ∈ s □ t ↔ ∃ x y, is_compl x y ∧ (∀ ⦃b⦄, a ⊓ x = b ⊓ x → b ∈ s) ∧ ∀ ⦃b⦄, a ⊓ y = b ⊓ y → b ∈ t :=
begin
  rw [certificator, mem_filter, and_iff_right_of_imp],
  rintro ⟨u, v, huv, hu, hv⟩,
  exact mem_inter.2 ⟨hu rfl, hv rfl⟩,
end

lemma certificator_subset_inter : s □ t ⊆ s ∩ t := filter_subset _ _
lemma certificator_subset_disj_sups : s □ t ⊆ s ○ t :=
begin
  simp_rw [subset_iff, mem_certificator, mem_disj_sups],
  rintro x ⟨u, v, huv, hu, hv⟩,
  refine ⟨x ⊓ u, hu inf_right_idem.symm, x ⊓ v, hv inf_right_idem.symm,
    huv.disjoint.mono inf_le_right inf_le_right, _⟩,
  rw [←inf_sup_left, huv.codisjoint.eq_top, inf_top_eq],
end

variables (s t u)

lemma certificator_comm : s □ t = t □ s :=
by { ext s, rw [mem_certificator, exists_comm], simp [is_compl_comm, and_comm] }

lemma _root_.is_upper_set.certificator_eq_inter (hs : is_upper_set (s : set α))
  (ht : is_lower_set (t : set α)) :
  s □ t = s ∩ t :=
begin
  refine certificator_subset_inter.antisymm (λ a ha, mem_certificator.2 ⟨a, aᶜ, is_compl_compl, _⟩),
  rw mem_inter at ha,
  simp only [@eq_comm _ ⊥, ←sdiff_eq, inf_idem, right_eq_inf, sdiff_self, sdiff_eq_bot_iff],
  exact ⟨λ b hab, hs hab ha.1, λ b hab, ht hab ha.2⟩,
end

lemma _root_.is_lower_set.certificator_eq_inter (hs : is_lower_set (s : set α))
  (ht : is_upper_set (t : set α)) :
  s □ t = s ∩ t :=
begin
  refine certificator_subset_inter.antisymm (λ a ha,
    mem_certificator.2 ⟨aᶜ, a, is_compl_compl.symm, _⟩),
  rw mem_inter at ha,
  simp only [@eq_comm _ ⊥, ←sdiff_eq, inf_idem, right_eq_inf, sdiff_self, sdiff_eq_bot_iff],
  exact ⟨λ b hab, hs hab ha.1, λ b hab, ht hab ha.2⟩,
end

lemma _root_.is_upper_set.certificator_eq_disj_sups (hs : is_upper_set (s : set α))
  (ht : is_upper_set (t : set α)) :
  s □ t = s ○ t :=
begin
  refine certificator_subset_disj_sups.antisymm (λ a ha, mem_certificator.2 _),
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_disj_sups.1 ha,
  refine ⟨x, xᶜ, is_compl_compl, _⟩,
  simp only [inf_of_le_right, le_sup_left, right_eq_inf, ←sdiff_eq, hxy.sup_sdiff_cancel_left],
  exact ⟨λ b hab, hs hab hx, λ b hab, ht (hab.trans_le sdiff_le) hy⟩,
end

end boolean_algebra

open_locale finset_family

variables [decidable_eq α] [fintype α] {𝒜 ℬ 𝒞 : finset (finset α)}

/-- The **Van den Berg-Kesten-Reimer Inequality**: The probability that `𝒜` and `ℬ` occur
"disjointly" is less than the product of their probabilities. -/
lemma card_certificator_le : 2 ^ fintype.card α * (𝒜 □ ℬ).card ≤ 𝒜.card * ℬ.card :=
sorry

end finset
