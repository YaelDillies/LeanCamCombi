import Mathlib.Data.Nat.Defs

namespace Nat
variable {m n : ℕ}

lemma pow_self_pos : ∀ n : ℕ, 0 < n ^ n
  | 0 => Nat.zero_lt_one
  | n + 1 => by simpa [Nat.pow_succ] using Nat.pow_pos n.succ_pos

lemma pow_self_mul_pow_self_le : m ^ m * n ^ n ≤ (m + n) ^ (m + n) := by
  rw [Nat.pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_add_right ..) _)
    (Nat.pow_le_pow_left (le_add_left ..) _)

end Nat
