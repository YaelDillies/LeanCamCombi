import Mathlib.Data.Set.Image

namespace Set
variable {α β γ γ₁ γ₂ δ δ₁ δ₂ : Type*} {h : β → α} {f : γ → β} {f₁ : γ₁ → α} {f₂ : γ → γ₁}
  {g : δ → β} {g₁ : δ₁ → α} {g₂ : δ → δ₁}

lemma image_of_range_union_range_eq_univ (hf : h ∘ f = f₁ ∘ f₂) (hg : h ∘ g = g₁ ∘ g₂)
    (hfg : range f ∪ range g = univ) (s : Set β) :
    h '' s = f₁ '' (f₂ '' (f ⁻¹' s)) ∪ g₁ '' (g₂ '' (g ⁻¹' s)) := by
  rw [← image_comp, ← image_comp, ← hf, ← hg, image_comp, image_comp, image_preimage_eq_inter_range,
    image_preimage_eq_inter_range, ← image_union, ← inter_union_distrib_left, hfg, inter_univ]

end Set
