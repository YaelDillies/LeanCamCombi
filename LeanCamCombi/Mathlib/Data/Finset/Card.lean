import Mathlib.Data.Finset.Card

namespace Finset

variable {α : Type*} [DecidableEq α] {s t : Finset α}

lemma card_sdiff_comm (h : s.card = t.card) : (s \ t).card = (t \ s).card := by
  have : (s \ t ∪ s ∩ t).card = (t \ s ∪ t ∩ s).card
  rwa [sdiff_union_inter, sdiff_union_inter]
  rwa [card_disjoint_union (disjoint_sdiff_inter _ _),
    card_disjoint_union (disjoint_sdiff_inter _ _), inter_comm, add_left_inj] at this

end Finset
