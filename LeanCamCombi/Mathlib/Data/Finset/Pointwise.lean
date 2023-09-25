import Mathlib.Data.Finset.Pointwise

open scoped Pointwise

variable {s : Set ℕ}

instance Nat.decidablePred_mem_vadd [DecidablePred (· ∈ s)] (a : ℕ) : DecidablePred (· ∈ a +ᵥ s) :=
  λ n ↦ decidable_of_iff' (a ≤ n ∧ n - a ∈ s) $ by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop
