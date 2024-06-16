import Mathlib.Data.Nat.Defs

namespace Nat

protected lemma min_left_comm (a b c : ℕ) : min a (min b c) = min b (min a c) := by
  rw [← Nat.min_assoc, ← Nat.min_assoc, b.min_comm]

protected lemma max_left_comm (a b c : ℕ) : max a (max b c) = max b (max a c) := by
  rw [← Nat.max_assoc, ← Nat.max_assoc, b.max_comm]

protected lemma min_right_comm (a b c : ℕ) : min (min a b) c = min (min a c) b := by
  rw [Nat.min_assoc, Nat.min_assoc, b.min_comm]

protected lemma max_right_comm (a b c : ℕ) : max (max a b) c = max (max a c) b := by
  rw [Nat.max_assoc, Nat.max_assoc, b.max_comm]

end Nat
