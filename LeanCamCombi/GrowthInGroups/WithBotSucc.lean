import Mathlib.Order.SuccPred.Basic
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

namespace WithBot
variable {α : Type*} [Preorder α] [OrderBot α] [SuccOrder α]

/-- The successor of `a : WithBot α` as an element of `α`. -/
def succ (a : WithBot α) : α := a.recBotCoe ⊥ Order.succ

@[simp] lemma succ_bot' : succ (⊥ : WithBot α) = ⊥ := rfl
@[simp] lemma succ_coe' (a : α) : succ (a : WithBot α) = Order.succ a := rfl

lemma succ_eq_succ : ∀ a : WithBot α, succ a = Order.succ a
  | ⊥ => rfl
  | (a : α) => rfl

lemma succ_mono : Monotone (succ : WithBot α → α)
  | ⊥, _, hab => by simp
  | (a : α), ⊥, hab => by simp at hab
  | (a : α), (b : α), hab => Order.succ_le_succ (by simpa using hab)

lemma succ_strictMono [NoMaxOrder α] : StrictMono (succ : WithBot α → α)
  | ⊥, (b : α), hab => by simp
  | (a : α), (b : α), hab => Order.succ_lt_succ (by simpa using hab)

@[gcongr]
lemma succ_le_succ {a b : WithBot α} (hab : a ≤ b) : a.succ ≤ b.succ :=
  succ_mono hab

@[gcongr]
lemma succ_lt_succ [NoMaxOrder α] {a b : WithBot α} (hab : a < b) : a.succ < b.succ :=
  succ_strictMono hab

end WithBot

namespace WithBot
variable {α : Type*} [Preorder α] [OrderBot α] [AddMonoidWithOne α] [SuccAddOrder α]

lemma succ_natCast (n : ℕ) :
    succ (n : WithBot α) = n + 1 := by
  rw [← WithBot.coe_natCast, succ_coe', Order.succ_eq_add_one]

@[simp]
lemma succ_zero : succ (0 : WithBot α) = 1 := by simpa using succ_natCast 0

@[simp]
lemma succ_one : succ (1 : WithBot α) = 2 := by
  simpa [one_add_one_eq_two] using succ_natCast 1

@[simp]
lemma succ_ofNat (n : ℕ) [n.AtLeastTwo] :
    succ (no_index OfNat.ofNat n : WithBot α) = OfNat.ofNat n + 1 :=
  succ_natCast n
