import Mathlib.Data.Subtype

namespace Subtype
variable {α : Type*} {p : α → Prop} {a b : {a // p a}}

lemma coe_ne_coe : (a : α) ≠ b ↔ a ≠ b := coe_inj.not

end Subtype
