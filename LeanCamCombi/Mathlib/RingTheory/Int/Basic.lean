import Mathlib.RingTheory.Int.Basic

namespace Nat

lemma prime_composite_induction {P : ℕ → Prop} (zero : P 0) (one : P 1)
    (prime : ∀ p : ℕ, p.Prime → P p) (composite : ∀ a, 2 ≤ a → P a → ∀ b, 2 ≤ b → P b → P (a * b))
    (n : ℕ) : P n := by
  refine induction_on_primes zero one ?_ _
  rintro p (_ | _ | a) hp ha
  · simpa
  · simpa using prime _ hp
  · exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha

end Nat
