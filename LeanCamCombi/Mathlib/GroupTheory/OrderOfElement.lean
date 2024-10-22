import Mathlib.GroupTheory.OrderOfElement

namespace CharP
variable {R : Type*} [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b n : ℕ}

lemma addOrderOf_natCast (hn : n ≠ 0) : addOrderOf (n : R) = p / p.gcd n := sorry

end CharP
