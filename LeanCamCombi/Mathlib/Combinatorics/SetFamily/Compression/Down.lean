import Mathlib.Combinatorics.SetFamily.Compression.Down
import LeanCamCombi.Mathlib.Data.Finset.Lattice
import LeanCamCombi.Mathlib.Data.Finset.Basic

namespace Finset
variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {a : α}

lemma memberSubfamily_image_insert (h𝒜 : ∀ s ∈ 𝒜, a ∉ s) :
    (𝒜.image $ insert a).memberSubfamily a = 𝒜 := by
  ext s
  simp only [mem_memberSubfamily, mem_image]
  refine ⟨?_, fun hs ↦ ⟨⟨s, hs, rfl⟩, h𝒜 _ hs⟩⟩
  rintro ⟨⟨t, ht, hts⟩, hs⟩
  rwa [←insert_erase_invOn.2.injOn (h𝒜 _ ht) hs hts]

@[simp] lemma nonMemberSubfamily_image_insert : (𝒜.image $ insert a).nonMemberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_not_mem]

@[simp] lemma memberSubfamily_image_erase : (𝒜.image (erase · a)).memberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_not_mem,
    (ne_of_mem_of_not_mem' (mem_insert_self _ _) (not_mem_erase _ _)).symm]

lemma image_insert_memberSubfamily (𝒜 : Finset (Finset α)) (a : α) :
    (𝒜.memberSubfamily a).image (insert a) = 𝒜.filter (a ∈ ·) := by
  ext s
  simp only [mem_memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun ⟨hs, ha⟩ ↦ ⟨erase s a, ⟨?_, not_mem_erase _ _⟩, insert_erase ha⟩⟩
  · rintro ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨hs, mem_insert_self _ _⟩
  · rwa [insert_erase ha]

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `𝒜 ∪ {s ∪ {a} | s ∈ ℬ}` assuming the property for `𝒜` and `ℬ`, where `a` is an element of the
  ground type and `𝒜` and `ℬ` are families of finsets not containing `a`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.family_induction_on.`-/
@[elab_as_elim]
lemma memberFamily_induction_on {p : Finset (Finset α) → Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.nonMemberSubfamily a) → p (𝒜.memberSubfamily a) → p 𝒜) : p 𝒜 := by
  set u := 𝒜.sup id
  have hu : ∀ s ∈ 𝒜, s ⊆ u := fun s ↦ le_sup (f := id)
  clear_value u
  induction' u using Finset.induction with a u _ ih generalizing 𝒜
  · simp_rw [subset_empty] at hu
    rw [←subset_singleton_iff', subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  refine subfamily a (ih _ ?_) (ih _ ?_)
  · simp only [mem_nonMemberSubfamily, and_imp]
    exact fun s hs has ↦ (subset_insert_iff_of_not_mem has).1 $ hu _ hs
  · simp only [mem_memberSubfamily, and_imp]
    exact fun s hs ha ↦ (insert_subset_insert_iff ha).1 $ hu _ hs

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `{s ∪ {a} | s ∈ 𝒜}` assuming the property for `𝒜` a family of finsets not containing `a`.
* `𝒜 ∪ ℬ` assuming the property for `𝒜` and `ℬ`, where `a` is an element of the
  ground type and `𝒜`is a family of finsets not containing `a` and `ℬ` a family of finsets
  containing `a`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.memberFamily_induction_on.`-/
@[elab_as_elim]
protected lemma family_induction_on {p : Finset (Finset α) → Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (image_insert : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      (∀ s ∈ 𝒜, a ∉ s) → p 𝒜 → p (𝒜.image $ insert a))
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.filter (a ∉ ·)) → p (𝒜.filter (a ∈ ·)) → p 𝒜) : p 𝒜 := by
  refine memberFamily_induction_on 𝒜 empty singleton_empty fun a 𝒜 h𝒜₀ h𝒜₁ ↦ subfamily a h𝒜₀ ?_
  rw [←image_insert_memberSubfamily]
  exact image_insert _ (by simp) h𝒜₁

end Finset
