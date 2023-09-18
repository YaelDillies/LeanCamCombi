import Mathlib.Data.Finset.Basic

-- attribute [protected] Finset.sdiff_self

-- TODO: Fix implicitness of `Finset.inter_eq_left_iff_subset`
-- TODO: Rename `Finset.union_eq_empty_iff` → `Finset.union_eq_empty`

namespace Finset
variable {α : Type*} [DecidableEq α] {s t : Finset α} {a : α}

instance instDecidableLE : @DecidableRel (Finset α) (· ≤ ·) := λ _ _ ↦ decidableSubsetFinset
instance instDecidableLT : @DecidableRel (Finset α) (· < ·) := λ _ _ ↦ decidableSSubsetFinset

lemma erase_eq_iff_eq_insert (hs : a ∈ s) (ht : a ∉ t) : erase s a = t ↔ s = insert a t := by
  have := insert_erase hs; aesop

lemma insert_erase_invOn :
    Set.InvOn (insert a) (λ s ↦ erase s a) {s : Finset α | a ∈ s} {s : Finset α | a ∉ s} :=
  ⟨λ _s ↦ insert_erase, λ _s ↦ erase_insert⟩

lemma insert_sdiff_cancel (ha : a ∉ s) : insert a s \ s = {a} := by
  rw [insert_sdiff_of_not_mem _ ha, Finset.sdiff_self, insert_emptyc_eq]

@[simp] lemma symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t := symmDiff_eq_bot
@[simp] lemma symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

end Finset
