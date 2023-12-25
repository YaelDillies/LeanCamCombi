import Mathlib.Data.Set.Image

#align_import mathlib.data.set.image

open Function

namespace Set

variable {α β : Type _} {f : α → β} {s : Set α}

theorem preimage_subset_of_subset_image {t : Set β} (hf : Injective f) (h : t ⊆ f '' s) :
    f ⁻¹' t ⊆ s := fun x hx => hf.mem_set_image.1 <| h hx

end Set
