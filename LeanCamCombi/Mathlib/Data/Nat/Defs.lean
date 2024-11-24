import Mathlib.Data.Nat.Defs

namespace Nat
variable {a b : ℕ}

-- TODO: Use `Ne` in `Nat.mod_two_ne_one`

lemma le_mul_div_add (hb : b ≠ 0) : a ≤ b * (a / b) + b - 1 := by
  refine Nat.le_sub_of_add_le ?_
  rw [succ_le_iff, ← Nat.mul_add_one, Nat.mul_comm, ← div_lt_iff_lt_mul (Nat.pos_iff_ne_zero.2 hb),
    Nat.lt_add_one_iff]

end Nat
