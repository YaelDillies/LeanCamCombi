import Mathlib.Data.Nat.Factorization.Basic
import LeanCamCombi.Mathlib.Data.Nat.Factors

namespace Nat
variable {n p : ℕ}

-- TODO: Rename `Nat.factors` to `Nat.primeFactorsList`
-- TODO: Protect `Nat.Prime.factorization`

def primeFactors (n : ℕ) : Finset ℕ := n.factors.toFinset

@[simp] lemma support_factorization' (n : ℕ) : (factorization n).support = n.primeFactors := rfl
@[simp] lemma toFinset_factors (n : ℕ) : n.factors.toFinset = n.primeFactors := rfl

@[simp] lemma mem_primeFactors : p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
  simp_rw [←toFinset_factors, List.mem_toFinset, mem_factors']

lemma mem_primeFactors_of_ne_zero (hn : n ≠ 0) : p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n := by
  simp [hn]

end Nat
