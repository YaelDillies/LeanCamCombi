import Mathlib.Data.Nat.Order.Lemmas

namespace Nat
variable {a b : ℕ}

protected lemma div_ne_zero (hb : b ≠ 0) : a / b ≠ 0 ↔ b ≤ a := by
  rw [ne_eq, Nat.div_eq_zero_iff hb.bot_lt, not_lt]

end Nat
