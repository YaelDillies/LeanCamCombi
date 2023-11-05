import Mathlib.Data.Set.Equitable

namespace Set
variable {α β : Type*} [LinearOrder β] [Add β] [One β] {s : Set α} {f : α → β}

@[simp]
lemma not_equitableOn : ¬s.EquitableOn f ↔ ∃ a ∈ s, ∃ b ∈ s, f b + 1 < f a := by
  simp [EquitableOn]; aesop

end Set
