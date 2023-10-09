import Mathlib.Algebra.Order.Group.Defs

section
variable {α : Type*} [CommGroup α] [LinearOrder α] [CovariantClass α α (· *  ·) (· ≤ ·)]
  {a b c d : α}

@[to_additive] lemma lt_or_lt_of_div_lt_div : a / d < b / c → a < b ∨ c < d := by
  contrapose!; exact fun h ↦ div_le_div'' h.1 h.2

end
