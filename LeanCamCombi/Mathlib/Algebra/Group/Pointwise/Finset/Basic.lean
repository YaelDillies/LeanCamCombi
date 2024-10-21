import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# TODO

Rename `empty_nsmul` to `nsmul_empty`
-/

open MulOpposite
open scoped Pointwise

variable {α : Type*}

namespace Finset

attribute [simp] singleton_one

section Mul
variable [DecidableEq α] [Mul α]

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Finset α) : {a} * s = a • s := singleton_mul _

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Finset α) (a : α) : s * {a} = op a • s := mul_singleton _

end Mul

section Monoid
variable [DecidableEq α] [Monoid α] {s : Finset α} {n : ℕ}

@[to_additive (attr := simp) nsmul_singleton]
lemma singleton_pow (a : α) : ∀ n, ({a} : Finset α) ^ n = {a ^ n}
  | 0 => by simp
  | n + 1 => by simp [pow_succ, singleton_pow _ n]

@[to_additive]
lemma card_pow_le : ∀ {n}, (s ^ n).card ≤ s.card ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_succ]; refine card_mul_le.trans (by gcongr; exact card_pow_le)

end Monoid

section CancelMonoid
variable [DecidableEq α] [CancelMonoid α] {s : Finset α} {m n : ℕ}

protected lemma Nonempty.card_pow_mono (hs : s.Nonempty) : Monotone fun n : ℕ ↦ (s ^ n).card :=
  monotone_nat_of_le_succ fun n ↦ by rw [pow_succ]; exact card_le_card_mul_right _ hs

lemma card_pow_mono (hm : m ≠ 0) (hmn : m ≤ n) : (s ^ m).card ≤ (s ^ n).card := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hm]
  · exact hs.card_pow_mono hmn

lemma card_le_card_pow (hn : n ≠ 0) : s.card ≤ (s ^ n).card := by
  simpa using card_pow_mono (s := s) one_ne_zero (Nat.one_le_iff_ne_zero.2 hn)

end CancelMonoid

section Group
variable [DecidableEq α] [DivisionMonoid α] {n : ℤ}

@[to_additive (attr := simp) zsmul_empty]
lemma empty_zpow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := by cases n <;> aesop

@[to_additive (attr := simp) zsmul_singleton]
lemma singleton_zpow (a : α) (n : ℤ) : ({a} : Finset α) ^ n = {a ^ n} := by cases n <;> simp

end Group
end Finset
