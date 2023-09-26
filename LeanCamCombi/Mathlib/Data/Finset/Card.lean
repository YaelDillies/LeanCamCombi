import Mathlib.Data.Finset.Card

namespace Finset

variable {α : Type*} [DecidableEq α] {s t : Finset α}

lemma card_sdiff_comm (h : s.card = t.card) : (s \ t).card = (t \ s).card :=
  add_left_injective t.card $ by simp_rw [card_sdiff_add_card, ←h, card_sdiff_add_card, union_comm]

end Finset
