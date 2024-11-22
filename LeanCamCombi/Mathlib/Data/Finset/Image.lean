import Mathlib.Data.Finset.Image

namespace Finset
variable {α β : Type*} [DecidableEq β] {f : α → β} {s : Finset α} {p : β → Prop}

lemma forall_mem_image : (∀ y ∈ s.image f, p y) ↔ ∀ ⦃x⦄, x ∈ s → p (f x) := by simp
lemma exists_mem_image : (∃ y ∈ s.image f, p y) ↔ ∃ x ∈ s, p (f x) := by simp

end Finset
