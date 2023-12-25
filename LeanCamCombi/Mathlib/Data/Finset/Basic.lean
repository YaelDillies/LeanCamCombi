import Mathlib.Data.Finset.Basic

#align_import mathlib.data.finset.basic

variable {α : Type _} [DecidableEq α] {s t : Finset α} {a : α}

namespace Finset

alias ⟨_, nonempty.attach⟩ := attach_nonempty_iff

attribute [protected] nonempty.attach

theorem insert_comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  coe_injective <| by push_cast; exact Set.insert_comm _ _ _

theorem disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.eraseₓ a) (insert a t) ↔ Disjoint s t := by
  rw [disjoint_erase_comm, erase_insert ha]

theorem disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.eraseₓ a) ↔ Disjoint s t := by
  rw [← disjoint_erase_comm, erase_insert ha]

end Finset
