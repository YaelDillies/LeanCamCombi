import Mathlib.Order.Synonym

namespace Lex
variable {α : Type*}

@[simp] lemma «forall» {p : Lex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toLex a) := Iff.rfl
@[simp] lemma «exists» {p : Lex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toLex a) := Iff.rfl

end Lex
