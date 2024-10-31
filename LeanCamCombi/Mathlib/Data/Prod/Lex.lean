import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.Common

namespace Prod.Lex
variable {α β : Type*} [PartialOrder α] [Preorder β]

lemma lt_iff' (x y : α × β) : toLex x < toLex y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 < y.2) := by
  rw [Prod.Lex.lt_iff]
  simp only [lt_iff_le_not_le, le_antisymm_iff]
  tauto

variable [WellFoundedLT α] [WellFoundedLT β]

instance : WellFoundedLT (α ×ₗ β) := instIsWellFoundedProdLex

end Prod.Lex
