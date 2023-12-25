import Mathlib.Data.Finset.Card

namespace Finset

variable {α : Type _} {s : Finset α} {a : α}

@[simp]
theorem one_le_card : 1 ≤ s.card ↔ s.Nonempty :=
  card_pos

end Finset
