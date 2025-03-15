import Mathlib.Data.Set.Function

namespace Set
variable {α β : Type*} {s t : Set α} {f : α → β}

lemma disjoint_image' (hf : (s ∪ t).InjOn f) : Disjoint (f '' s) (f '' t) ↔ Disjoint s t where
  mp := .of_image
  mpr hst := disjoint_image_image fun _a ha _b hb ↦
    hf.ne (.inl ha) (.inr hb) fun H ↦ Set.disjoint_left.1 hst ha (H ▸ hb)

end Set
