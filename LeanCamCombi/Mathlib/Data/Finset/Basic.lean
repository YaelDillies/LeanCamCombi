import Mathlib.Data.Finset.Basic

-- TODO: Rename `Finset.union_eq_empty_iff` → `Finset.union_eq_empty`

attribute [simp] Set.insert_subset_insert_iff

namespace Finset
variable {α : Type*} [DecidableEq α] {s t : Finset α} {a : α}

@[simp] lemma insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  simp_rw [←coe_subset]; simp [-coe_subset, ha]

end Finset
