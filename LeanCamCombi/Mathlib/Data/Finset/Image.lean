import Mathlib.Data.Finset.Image
import LeanCamCombi.Mathlib.Data.Set.Function

namespace Finset
variable {α β : Type*} [DecidableEq β] {f : α → β} {s : Finset α} {p : β → Prop}

lemma forall_mem_image : (∀ y ∈ s.image f, p y) ↔ ∀ ⦃x⦄, x ∈ s → p (f x) := by simp
lemma exists_mem_image : (∃ y ∈ s.image f, p y) ↔ ∃ x ∈ s, p (f x) := by simp

end Finset

namespace Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {s t : Finset α} {f : α → β}

lemma image_sdiff_of_injOn (hf : Set.InjOn f s) (hts : t ⊆ s) :
    (s \ t).image f = s.image f \ t.image f :=
  mod_cast Set.image_diff_of_injOn hf <| coe_subset.2 hts

end Finset
