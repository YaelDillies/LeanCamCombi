import Mathlib.Data.Finset.Slice

namespace Set
variable {α : Type*} {s : Finset α} {r : ℕ}

@[simp] lemma sized_empty : (∅ : Set (Finset α)).Sized r := by simp [Sized]
@[simp] lemma sized_singleton : ({s} : Set (Finset α)).Sized r ↔ s.card = r := by simp [Sized]

-- TODO: Fix `_root_` misport
alias _root_.Set.Sized.card_le := Finset.Set.Sized.card_le

end Set
