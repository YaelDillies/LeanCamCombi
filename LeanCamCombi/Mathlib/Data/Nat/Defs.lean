import Mathlib.Data.Nat.Defs

namespace Nat
variable {a b : ℕ}

@[simp] protected lemma div_eq_zero : a / b = 0 ↔ b = 0 ∨ a < b where
  mp h := by
    rw [← mod_add_div a b, h, Nat.mul_zero, Nat.add_zero, or_iff_not_imp_left]
    exact mod_lt _ ∘ Nat.pos_iff_ne_zero.2
  mpr := by
    obtain rfl | hb := eq_or_ne b 0
    · simp
    simp only [hb, false_or]
    rw [← Nat.mul_right_inj hb, ← Nat.add_left_cancel_iff, mod_add_div]
    simp +contextual [mod_eq_of_lt]

protected lemma div_ne_zero {a b : ℕ} : a / b ≠ 0 ↔ b ≠ 0 ∧ b ≤ a := by simp

@[simp] protected lemma div_pos' {a b : ℕ} : 0 < a / b ↔ 0 < b ∧ b ≤ a := by
  simp [Nat.pos_iff_ne_zero]

end Nat
