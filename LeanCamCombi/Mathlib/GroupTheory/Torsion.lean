import Mathlib.GroupTheory.Torsion

namespace Monoid
variable {α : Type*} [Monoid α]

@[to_additive (attr := simp)]
lemma isTorsionFree_of_subsingleton [Subsingleton α] : IsTorsionFree α :=
  fun _a ha _ => ha <| Subsingleton.elim _ _

end Monoid
