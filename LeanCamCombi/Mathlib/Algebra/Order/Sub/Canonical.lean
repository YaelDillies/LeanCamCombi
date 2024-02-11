import Mathlib.Algebra.Order.Sub.Canonical

attribute [simp] tsub_lt_self_iff

section
variable {α : Type*} [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α]
  [ContravariantClass α α (· + ·) (· ≤ ·)]

-- TODO: Rename `AddGroup.toHasOrderedSub` to `AddGroup.toOrderedSub`

lemma tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b := by
  rw [tsub_eq_tsub_min _ b, tsub_tsub_cancel_of_le (min_le_left a _)]

end
