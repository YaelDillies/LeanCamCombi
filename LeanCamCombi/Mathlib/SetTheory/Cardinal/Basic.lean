import Mathlib.SetTheory.Cardinal.Basic

open Set

universe u

namespace Cardinal

@[simp] lemma mk_setProd {α β : Type u} (s : Set α) (t : Set β) : #(s ×ˢ t) = #s * #t := by
  rw [mul_def, mk_congr (Equiv.Set.prod ..)]

lemma mk_image2_le {α β γ : Type u} {f : α → β → γ} {s : Set α} {t : Set β} :
    #(image2 f s t) ≤ #s * #t := by
  rw [← image_uncurry_prod, ← mk_setProd]
  exact mk_image_le

end Cardinal
