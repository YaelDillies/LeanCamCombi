import Mathlib.NumberTheory.Fermat

open Finset Function
open scoped BigOperators

namespace Nat
variable {m n : ℕ}

-- TODO: Replace
alias fermatNumber_strictMono := strictMono_fermatNumber

lemma fermatNumber_mono : Monotone fermatNumber := fermatNumber_strictMono.monotone
lemma fermatNumber_injective : Injective fermatNumber := fermatNumber_strictMono.injective

@[simp]
lemma fermatNumber_inj : fermatNumber m = fermatNumber n ↔ m = n := fermatNumber_injective.eq_iff

lemma three_le_fermatNumber (n : ℕ) : 3 ≤ fermatNumber n := fermatNumber_mono n.zero_le

lemma fermatNumber_ne_one (n : ℕ) : fermatNumber n ≠ 1 :=
  (n.three_le_fermatNumber.trans_lt' $ by norm_num).ne'

/-- The recurence relation satisfied by Fermat numbers. -/
lemma prod_fermatNumber_add_two (n : ℕ) : ∏ k in range n, fermatNumber k + 2 = fermatNumber n := by
  zify
  induction' n with n ih
  · trivial
  rw [prod_range_succ, eq_sub_iff_add_eq.2 ih]
  -- We prove a form without subtraction of naturals
  have h : fermatNumber n * fermatNumber n + 2 = fermatNumber n.succ + 2 * fermatNumber n := by
    unfold fermatNumber; simp only [_root_.pow_succ, two_mul]; ring
  -- Then we let linarith finish
  linarith

-- TODO: Replace
alias prod_fermatNumber := fermatNumber_product

-- TODO: Replace `coprime_fermatNumber_fermatNumber`!
/-- Fermat numbers are coprime.

This follows from the recurrence relations and divisibility,
as well as the parity of Fermat numbers.
-/
lemma pairwise_coprime_fermatNumber :
    Pairwise fun m n ↦ Coprime (fermatNumber m) (fermatNumber n) := by
  rintro m n hmn
  exact coprime_fermatNumber_fermatNumber hmn.symm
