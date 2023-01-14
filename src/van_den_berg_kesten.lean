/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.sort
import data.finset.sups
import data.fintype.basic
import mathlib.order
import order.upper_lower

/-!
# Set family certificates

-/

open_locale finset_family

variables {α : Type*} [decidable_eq α] [fintype α]

namespace finset
variables (𝒜 ℬ 𝒞 : finset (finset α)) {s : finset α}

def certificator : finset (finset α) :=
(𝒜 ∩ ℬ).filter $ λ s, ∃ u v, is_compl u v ∧ (∀ ⦃t⦄, s ∩ u = t ∩ u → t ∈ 𝒜) ∧
  ∀ ⦃t⦄, s ∩ v = t ∩ v → t ∈ ℬ

localized "infix (name := finset.certificator) ` □ `:70 := certificator" in finset_family

variables {𝒜 ℬ 𝒞}

@[simp] lemma mem_certificator :
  s ∈ 𝒜 □ ℬ ↔ ∃ u v, is_compl u v ∧ (∀ ⦃t⦄, s ∩ u = t ∩ u → t ∈ 𝒜) ∧
    ∀ ⦃t⦄, s ∩ v = t ∩ v → t ∈ ℬ :=
begin
  rw [certificator, mem_filter, and_iff_right_of_imp],
  rintro ⟨u, v, huv, hu, hv⟩,
  exact mem_inter.2 ⟨hu rfl, hv rfl⟩,
end

lemma certificator_subset_inter : 𝒜 □ ℬ ⊆ 𝒜 ∩ ℬ := filter_subset _ _
lemma certificator_subset_disj_sups : 𝒜 □ ℬ ⊆ 𝒜 ○ ℬ :=
begin
  simp_rw [subset_iff, mem_certificator, mem_disj_sups],
  rintro x ⟨u, v, huv, hu, hv⟩,
  refine ⟨x ∩ u, hu (inter_right_idem _ _).symm, x ∩ v, hv (inter_right_idem _ _).symm,
    huv.disjoint.mono (inter_subset_right _ _) (inter_subset_right _ _), _⟩,
  rw [←inter_distrib_left, ←sup_eq_union, huv.codisjoint.eq_top, top_eq_univ, inter_univ],
end

variables (𝒜 ℬ 𝒞)

lemma certificator_comm : 𝒜 □ ℬ = ℬ □ 𝒜 :=
by { ext s, rw [mem_certificator, exists_comm], simp [is_compl_comm, and_comm] }

lemma _root_.is_upper_set.certificator_eq_inter (h𝒜 : is_upper_set (𝒜 : set (finset α)))
  (hℬ : is_lower_set (ℬ : set (finset α))) :
  𝒜 □ ℬ = 𝒜 ∩ ℬ :=
begin
  refine certificator_subset_inter.antisymm (λ s hs, mem_certificator.2 ⟨s, sᶜ, is_compl_compl, _⟩),
  rw mem_inter at hs,
  simp only [@eq_comm _ s, @eq_comm _ ∅, ←sdiff_eq_inter_compl, inter_self,
    inter_eq_right_iff_subset, sdiff_self, sdiff_eq_empty_iff_subset],
  exact ⟨λ t hst, h𝒜 hst hs.1, λ t hst, hℬ hst hs.2⟩,
end

lemma _root_.is_lower_set.certificator_eq_inter (h𝒜 : is_lower_set (𝒜 : set (finset α)))
  (hℬ : is_upper_set (ℬ : set (finset α))) :
  𝒜 □ ℬ = 𝒜 ∩ ℬ :=
begin
  refine certificator_subset_inter.antisymm (λ s hs,
    mem_certificator.2 ⟨sᶜ, s, is_compl_compl.symm, _⟩),
  rw mem_inter at hs,
  simp only [@eq_comm _ s, @eq_comm _ ∅, ←sdiff_eq_inter_compl, inter_self,
    inter_eq_right_iff_subset, sdiff_self, sdiff_eq_empty_iff_subset],
  exact ⟨λ t hst, h𝒜 hst hs.1, λ t hst, hℬ hst hs.2⟩,
end

lemma _root_.is_upper_set.certificator_eq_disj_sups (h𝒜 : is_upper_set (𝒜 : set (finset α)))
  (hℬ : is_upper_set (ℬ : set (finset α))) :
  𝒜 □ ℬ = 𝒜 ○ ℬ :=
begin
  refine certificator_subset_disj_sups.antisymm (λ s hs, mem_certificator.2 _),
  obtain ⟨u, hu, v, hv, huv, rfl⟩ := mem_disj_sups.1 hs,
  refine ⟨u, uᶜ, is_compl_compl, _⟩,
  simp,
  simp only [@eq_comm _ (u ∪ v), @eq_comm _ ∅, ←sdiff_eq_inter_compl, inter_self,
    inter_eq_right_iff_subset, sdiff_self, sdiff_eq_empty_iff_subset],
  exact ⟨λ t hst, h𝒜 hst hu, λ t hst, hℬ hst hs.2⟩,
end

lemma _root_.is_lower_set.certificator_eq_inter (h𝒜 : is_lower_set (𝒜 : set (finset α)))
  (hℬ : is_upper_set (ℬ : set (finset α))) :
  𝒜 □ ℬ = 𝒜 ∩ ℬ :=
begin
  refine certificator_subset_inter.antisymm (λ s hs,
    mem_certificator.2 ⟨sᶜ, s, is_compl_compl.symm, _⟩),
  rw mem_inter at hs,
  simp only [@eq_comm _ s, @eq_comm _ ∅, ←sdiff_eq_inter_compl, inter_self,
    inter_eq_right_iff_subset, sdiff_self, sdiff_eq_empty_iff_subset],
  exact ⟨λ t hst, h𝒜 hst hs.1, λ t hst, hℬ hst hs.2⟩,
end

variables {𝒜 ℬ 𝒞}

lemma card_certificator_le (h𝒜 : is_upper_set (𝒜 : set (finset α)))
  (hℬ : is_upper_set (ℬ : set (finset α))) :
  2 ^ fintype.card α * (𝒜 □ ℬ).card ≤ 𝒜.card * ℬ.card :=
begin

end

end finset
