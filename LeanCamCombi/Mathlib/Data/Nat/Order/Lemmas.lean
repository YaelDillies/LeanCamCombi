import Mathlib.Data.Nat.Order.Lemmas

namespace Nat
variable {a b : ℕ}

protected lemma div_ne_zero_iff (hb : b ≠ 0) : a / b ≠ 0 ↔ b ≤ a := by
  rw [ne_eq, Nat.div_eq_zero_iff hb.bot_lt, not_lt]

protected lemma div_pos_iff (hb : b ≠ 0) : 0 < a / b ↔ b ≤ a := by
  rw [pos_iff_ne_zero, Nat.div_ne_zero_iff hb]

end Nat
