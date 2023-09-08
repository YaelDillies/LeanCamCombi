import Mathlib.Data.Fintype.Basic

namespace Finset

variable {α : Type _} {p : α → Prop} [DecidablePred p] {s : Finset α} [Fintype { a // p a }]

@[simp] lemma subtype_eq_univ : s.subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [ext_iff]
@[simp] lemma subtype_univ [Fintype α] : univ.subtype p = univ := by simp

end Finset
