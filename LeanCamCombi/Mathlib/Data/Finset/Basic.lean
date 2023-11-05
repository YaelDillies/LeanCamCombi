import Mathlib.Data.Finset.Basic

variable {α : Type*} [DecidableEq α] {s t : Finset α} {a : α}

namespace Finset

protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

lemma disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.erase a) (insert a t) ↔ Disjoint s t := by
  rw [disjoint_erase_comm, erase_insert ha]

lemma disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.erase a) ↔ Disjoint s t := by
  rw [← disjoint_erase_comm, erase_insert ha]

end Finset
