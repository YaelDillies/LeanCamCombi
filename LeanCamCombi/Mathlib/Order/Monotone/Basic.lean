import Mathlib.Order.Monotone.Basic

lemma Nat.pow_self_mono : Monotone fun n : ℕ ↦ n ^ n := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [Nat.pow_succ]
  exact (Nat.pow_le_pow_left n.le_succ _).trans (Nat.le_mul_of_pos_right _ n.succ_pos)
