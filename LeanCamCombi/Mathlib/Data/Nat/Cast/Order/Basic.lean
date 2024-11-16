import Mathlib.Data.Nat.Cast.Order.Basic

@[simp]
lemma Nat.cast_nonpos {α : Type*} [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α]
    [ZeroLEOneClass α] [CharZero α] {n : ℕ} : (n : α) ≤ 0 ↔ n ≤ 0 := by norm_cast
