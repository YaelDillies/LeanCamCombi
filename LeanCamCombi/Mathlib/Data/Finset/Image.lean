import Mathlib.Data.Finset.Image

open Function

namespace Finset
variable {α β : Type*} [DecidableEq β] {f : α → β}

lemma image_filter' (s : Finset α) (f : α → β) (p : β → Prop) [DecidablePred p] :
    (s.image f).filter p = (s.filter λ a ↦ p $ f a).image f :=
  image_filter

lemma _root_.Function.Injective.finset_image (hf : Injective f) : Injective (image f) :=
  λ s t hst ↦ coe_injective $ hf.image_injective $ by simpa using coe_inj.2 hst

end Finset
