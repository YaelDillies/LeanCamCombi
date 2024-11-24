import Mathlib.Data.Set.Image

open Function

namespace Set
variable {α β : Type*} {f : α → β} {s : Set α}

lemma preimage_subset_of_subset_image {t : Set β} (hf : Injective f) (h : t ⊆ f '' s) :
    f ⁻¹' t ⊆ s := fun _x hx => hf.mem_set_image.1 <| h hx

lemma image_compl_eq_range_sdiff_image (hf : Injective f) (s : Set α) :
    f '' sᶜ = range f \ f '' s := by rw [← image_univ, ← image_diff hf, compl_eq_univ_diff]

end Set
