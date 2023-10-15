import Mathlib.Combinatorics.SetFamily.Shadow

open Nat
open scoped FinsetFamily

namespace Finset
variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {s t : Finset α} {r k : ℕ}

@[simp] lemma shadow_iterate_empty (k : ℕ) : ∂^[k] (∅ : Finset (Finset α)) = ∅ := by
  induction' k <;> simp [*, shadow_empty]

/-- `t ∈ ∂𝒜` iff `t` is exactly one element less than something from `𝒜` -/
lemma mem_shadow_iff_exists_sdiff : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ (s \ t).card = 1 := by
  simp_rw [mem_shadow_iff_insert_mem, card_eq_one]
  constructor
  · rintro ⟨i, hi, ht⟩
    exact ⟨insert i t, ht, subset_insert _ _, i, insert_sdiff_cancel hi⟩
  · rintro ⟨s, hs, hts, a, ha⟩
    refine' ⟨a, (mem_sdiff.1 $ (ext_iff.1 ha _).2 $ mem_singleton_self _).2, _⟩
    rwa [insert_eq, ←ha, sdiff_union_of_subset hts]

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something from `𝒜`. -/
lemma mem_shadow_iterate_iff_exists_sdiff {𝒜 : Finset (Finset α)} {t : Finset α} (k : ℕ) :
    t ∈ ∂^[k] 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ (s \ t).card = k := by
  induction' k with k ih generalizing 𝒜 t
  · simp only [sdiff_eq_empty_iff_subset, Function.iterate_zero, id.def, card_eq_zero, exists_prop]
    refine' ⟨fun p ↦ ⟨t, p, Subset.rfl, Subset.rfl⟩, _⟩
    rintro ⟨s, hs, hst, hts⟩
    rwa [subset_antisymm hst hts]
  simp only [exists_prop, Function.comp_apply, Function.iterate_succ, ih,
    mem_shadow_iff_insert_mem]
  clear ih
  constructor
  · rintro ⟨s, ⟨a, ha, hs⟩, hts, rfl⟩
    refine' ⟨_, hs, hts.trans $ subset_insert _ _, _⟩
    rw [insert_sdiff_of_not_mem _ $ not_mem_mono hts ha,
      card_insert_of_not_mem $ not_mem_mono (sdiff_subset _ _) ha]
  · rintro ⟨s, hs, hts, hk⟩
    obtain ⟨a, ha⟩ : (s \ t).Nonempty := by rw [←card_pos, hk]; exact Nat.succ_pos _
    refine' ⟨erase s a, ⟨a, not_mem_erase _ _, _⟩, subset_erase.2 ⟨hts, (mem_sdiff.1 ha).2⟩, _⟩
    · rwa [insert_erase (mem_sdiff.1 ha).1]
    · rw [erase_sdiff_comm, card_erase_of_mem ha, hk, succ_sub_one]

/-- Everything in the `k`-th shadow is `k` smaller than things in the original. -/
lemma _root_.Set.Sized.shadow_iterate (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂^[k] 𝒜 : Set (Finset α)).Sized (r - k) := by
  simp_rw [Set.Sized, mem_coe, mem_shadow_iterate_iff_exists_sdiff]
  rintro t ⟨s, hs, hts, rfl⟩
  rw [card_sdiff hts, ←h𝒜 hs, Nat.sub_sub_self (card_le_of_subset hts)]

-- TODO: Fix `_root_` misport
alias _root_.Set.Sized.shadow := Set.Sized.shadow

end Finset
