import Mathlib.Data.Finset.Image

open Function

namespace Finset
variable {α β : Type*} [DecidableEq β] {f : α → β}

lemma image_filter' (s : Finset α) (f : α → β) (p : β → Prop) [DecidablePred p] :
    (s.image f).filter p = (s.filter λ a ↦ p $ f a).image f :=
  image_filter

end Finset
