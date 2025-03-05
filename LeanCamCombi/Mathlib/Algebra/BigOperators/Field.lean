import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Density

namespace Finset
variable {α β : Type*} [Fintype β]

@[simp]
lemma dens_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).dens = ∑ a ∈ s, (t a).dens := by simp [dens, sum_div]

variable {s : Finset α} {t : α → Finset β}

lemma dens_biUnion [DecidableEq β] (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (t x) (t y)) :
    (s.biUnion t).dens = ∑ u ∈ s, (t u).dens := by
  simp [dens, card_biUnion h, sum_div]

lemma dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens ≤ ∑ a ∈ s, (t a).dens := by
  simp only [dens, ← sum_div]
  gcongr
  · positivity
  · exact mod_cast card_biUnion_le

lemma dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β → α} {t : Finset β} (h : ∀ x ∈ t, f x ∈ s) :
    t.dens = ∑ a ∈ s, {b ∈ t | f b = a}.dens := by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]

lemma dens_eq_sum_dens_image [DecidableEq α] (f : β → α) (t : Finset β) :
    t.dens = ∑ a ∈ t.image f, {b ∈ t | f b = a}.dens :=
  dens_eq_sum_dens_fiberwise fun _ ↦ mem_image_of_mem _

end Finset
