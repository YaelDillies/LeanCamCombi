import Mathlib.Data.Nat.Factors

namespace Nat
variable {p n : ℕ}

@[simp] lemma mem_factors' : p ∈ n.factors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
  cases n <;> simp [mem_factors, *]

end Nat
