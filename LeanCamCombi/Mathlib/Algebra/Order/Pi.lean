import Mathlib.Algebra.Order.Pi
import LeanCamCombi.Mathlib.Order.Basic

open scoped Classical

namespace Function
variable {α β γ : Type*} [Zero γ] [LE γ] {f : α → β} {g : α → γ} {e : β → γ}

lemma extend_nonneg (hg : 0 ≤ g) (he : 0 ≤ e) : 0 ≤ extend f g e :=
  λ _b ↦ dite_nonneg (λ _ ↦ hg _) (λ _ ↦ he _)

end Function
