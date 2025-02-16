import Mathlib.Data.Fintype.Card

namespace Fintype
variable {α : Type*} {p : α → Prop}

-- TODO: Replace `card_subtype_le`
lemma card_subtype_le' [Fintype α] [Fintype {a // p a}] : card {a // p a} ≤ card α := by
  classical convert card_subtype_le _; infer_instance

end Fintype
