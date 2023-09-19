import Mathlib.Order.Basic

variable {α : Type*} [Zero α] {p : Prop} [Decidable p]

section
variable {a : p → α} {b : ¬ p → α}

lemma dite_nonneg [LE α] (ha : ∀ h, 0 ≤ a h) (hb : ∀ h, 0 ≤ b h) : 0 ≤ dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]
lemma dite_pos [LT α] (ha : ∀ h, 0 < a h) (hb : ∀ h, 0 < b h) : 0 < dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

end

section
variable {a b : α}

lemma ite_nonneg [LE α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by split <;> assumption
lemma ite_pos [LT α] (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by split <;> assumption

end
