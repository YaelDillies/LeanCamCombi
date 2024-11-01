import Mathlib.Data.Set.Image

open Function

namespace Set
variable {α β : Type*} {f : α → β}

lemma image_compl_eq_range_sdiff_image (hf : Injective f) (s : Set α) :
    f '' sᶜ = range f \ f '' s := by rw [← image_univ, ← image_diff hf, compl_eq_univ_diff]

end Set
