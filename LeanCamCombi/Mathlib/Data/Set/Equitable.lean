import Mathlib.Data.Set.Equitable

#align_import mathlib.data.set.equitable

namespace Set

variable {α β : Type _} [LinearOrder β] [Add β] [One β] {s : Set α} {f : α → β}

#print Set.not_equitableOn /-
@[simp]
theorem not_equitableOn : ¬s.EquitableOn f ↔ ∃ a ∈ s, ∃ b ∈ s, f b + 1 < f a := by
  simp [equitable_on]
-/

end Set
