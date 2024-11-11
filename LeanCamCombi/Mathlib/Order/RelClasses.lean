import Mathlib.Order.RelClasses

variable {α : Type*} [LT α] [WellFoundedLT α] {C : α → Prop}

-- TODO: Replace in mathlib
lemma WellFoundedLT.induction' (a : α) (ind : ∀ x, (∀ y < x, C y) → C x) : C a := induction a ind
