import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

open scoped Pointwise

namespace Set
variable {α : Type*}

section CommMonoid
variable [CommMonoid α] {s t : Set α} {a : α} {n : ℕ}

@[to_additive]
lemma mem_pow_iff_prod : ∀ {n}, a ∈ s ^ n ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ ∏ i, f i = a
  | 0 => by simp [eq_comm]
  | n + 1 => by
    simp_rw [pow_succ, mem_mul]
    sorry

end CommMonoid
end Set
