import Mathlib.Data.Fintype.Basic

namespace Finset
variable {α : Type*} [Fintype α] [DecidableEq α] {s t : Finset α} {a : α}

lemma subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ := le_compl_iff_le_compl (α := Finset α)

@[simp] lemma subset_compl_singleton : s ⊆ {a}ᶜ ↔ a ∉ s := by
  rw [subset_compl_comm,singleton_subset_iff, mem_compl]

end Finset
