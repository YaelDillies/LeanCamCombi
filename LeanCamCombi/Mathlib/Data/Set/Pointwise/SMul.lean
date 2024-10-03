import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open MulOpposite
open scoped Pointwise

namespace Set
variable {α : Type*}

section Mul
variable [Mul α]

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Set α) : {a} * s = a • s := singleton_mul

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Set α) (a : α) : s * {a} = op a • s := mul_singleton

end Mul
end Set
