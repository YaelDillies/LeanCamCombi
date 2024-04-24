import Mathlib.Data.Nat.Defs

namespace Nat
variable {a b : ℕ}

lemma eq_of_dvd_of_lt_two_mul (ha : a ≠ 0) (hdvd : b ∣ a) (hlt : a < 2 * b) : a = b := by
  obtain ⟨_ | _ | c, rfl⟩ := hdvd
  · simp at ha
  · exact Nat.mul_one _
  · rw [Nat.mul_comm] at hlt
    cases Nat.not_le_of_lt hlt (Nat.mul_le_mul_right _ (by omega))

end Nat
