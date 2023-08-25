import Mathbin.Data.Fintype.Basic

#align_import mathlib.data.fintype.basic

namespace Finset

variable {α : Type _} {p : α → Prop} [DecidablePred p] {s : Finset α} [Fintype { a // p a }]

@[simp]
theorem subtype_eq_univ : s.Subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [ext_iff]

@[simp]
theorem subtype_univ [Fintype α] : univ.Subtype p = univ := by simp

end Finset

