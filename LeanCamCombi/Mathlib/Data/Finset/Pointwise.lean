import Mathlib.Data.Finset.Pointwise

open MulOpposite
open scoped Pointwise

variable {α : Type*} {s : Set ℕ}

instance Nat.decidablePred_mem_vadd [DecidablePred (· ∈ s)] (a : ℕ) : DecidablePred (· ∈ a +ᵥ s) :=
  fun n ↦ decidable_of_iff' (a ≤ n ∧ n - a ∈ s) $ by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop

namespace Finset
section One
variable [One α] {s : Finset α}

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

end One

section Mul
variable [DecidableEq α] [Mul α]

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Finset α) : {a} * s = a • s := singleton_mul _

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Finset α) (a : α) : s * {a} = op a • s := mul_singleton _

end Mul
end Finset
