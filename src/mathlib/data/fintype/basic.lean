import data.fintype.basic

namespace finset
variables {α : Type*} {p : α → Prop} [decidable_pred p] {s : finset α} [fintype {a // p a}]

@[simp] lemma subtype_eq_univ : s.subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [ext_iff]

@[simp] lemma subtype_univ [fintype α] : univ.subtype p = univ := by simp

end finset
