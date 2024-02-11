import Mathlib.Data.Nat.Order.Lemmas

namespace Nat
variable {a b : ℕ}

lemma eq_of_dvd_of_lt_two_mul (ha : a ≠ 0) (hdvd : b ∣ a) (hlt : a < 2 * b) : a = b := by
  obtain ⟨_ | _ | c, rfl⟩ := hdvd
  · simp at ha
  · exact mul_one _
  · cases hlt.not_le ((mul_comm _ _).trans_le $ mul_le_mul_left' (by omega) _)

end Nat
