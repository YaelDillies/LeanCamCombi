/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Six proofs of the inﬁnity of primes : 2nd proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize the "Second proof",
which makes use of Fermat numbers.

This proof is based on the formalization of Moritz Firsching,
who's orginial work can be found on the repository at:
https://github.com/eric-wieser/formal_book

We've made some modifications and additions.

## Structure

- `second_proof`:
      The conclusion of our work. We show that we can form
      a (infinite) sequence of primes all pairwise different.
- `second_proof_standardised` :
      Infinitude of primes in terms of `set.infinite`,
      proven with `second_proof`.
- `F` :
      denotes  the Fermat number sequence.
- `fermat_product` :
      the recurrence relation satisfied by the Fermat numbers.
- `fermat_coprimes` :
      We show that the Fermat numbers are pairwise coprime.
      This is the the key step in showing infinitude of primes,
      as these numbers must have prime divisors, which must be
      pairwise different due to dividing coprime numbers.

-/

-- TODO: Protect `Nat.pow_succ`/`Nat.pow_succ'`, `Nat.ne_of_gt`

namespace Nat
variable {a a₁ a₂ b b₁ b₂ c n : ℕ}

lemma add_coprime_iff_left (h : c ∣ b) : Coprime (a + b) c ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp

lemma add_coprime_iff_right (h : c ∣ a) : Coprime (a + b) c ↔ Coprime b c := by
  obtain ⟨n, rfl⟩ := h; simp

lemma coprime_add_iff_left (h : a ∣ c) : Coprime a (b + c) ↔ Coprime a b := by
  obtain ⟨n, rfl⟩ := h; simp

lemma coprime_add_iff_right (h : a ∣ b) : Coprime a (b + c) ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp

@[simp] lemma two_coprime : Coprime 2 n ↔ Odd n := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := even_or_odd n <;> simp [← two_mul]

@[simp] lemma coprime_two : Coprime n 2 ↔ Odd n := coprime_comm.trans two_coprime

-- TODO: Replace `Nat.Coprime.coprime_dvd_left`
lemma Coprime.of_dvd_left (ha : a₁ ∣ a₂) (h : Coprime a₂ b) : Coprime a₁ b := h.coprime_dvd_left ha

-- TODO: Replace `Nat.Coprime.coprime_dvd_right`
lemma Coprime.of_dvd_right (hb : b₁ ∣ b₂) (h : Coprime a b₂) : Coprime a b₁ :=
  h.coprime_dvd_right hb

lemma Coprime.of_dvd (ha : a₁ ∣ a₂) (hb : b₁ ∣ b₂) (h : Coprime a₂ b₂) : Coprime a₁ b₁ :=
  (h.of_dvd_left ha).of_dvd_right hb

end Nat

open Finset Function
open scoped BigOperators

namespace Nat
variable {m n : ℕ}

/-- The Fermat numbers. -/
def fermat (n : ℕ) : ℕ := 2 ^ 2 ^ n + 1

/-- An evaluation lemma-/
lemma fermat_zero : fermat 0 = 3 := rfl

lemma fermat_strictMono : StrictMono fermat :=
  fun _m _n hmn ↦ add_lt_add_right (pow_lt_pow_right one_lt_two $ pow_lt_pow_right one_lt_two hmn) _

lemma fermat_mono : Monotone fermat := fermat_strictMono.monotone
lemma fermat_injective : Injective fermat := fermat_strictMono.injective

@[simp] lemma fermat_inj : fermat m = fermat n ↔ m = n := fermat_injective.eq_iff

lemma three_le_fermat (n : ℕ) : 3 ≤ fermat n := fermat_mono n.zero_le
lemma fermat_ne_one (n : ℕ) : fermat n ≠ 1 := (n.three_le_fermat.trans_lt' $ by norm_num).ne'

/-- Fermat numbers are odd-/
lemma fermat_odd (n : ℕ) : Odd (fermat n) :=
  ⟨2 ^ (2 ^ n - 1), by simpa [fermat, ← _root_.pow_succ, eq_comm]
    using tsub_add_cancel_of_le (one_le_pow _ _ zero_lt_two)⟩

/-- The recurence relation satisfied by Fermat numbers. -/
lemma prod_fermat_add_two (n : ℕ) : ∏ k in range n, fermat k + 2 = fermat n := by
  zify
  induction' n with n ih
  · trivial
  rw [prod_range_succ, eq_sub_iff_add_eq.2 ih]
  -- We prove a form without subtraction of naturals
  have h : fermat n * fermat n + 2 = fermat n.succ + 2 * fermat n := by
    unfold fermat; simp only [_root_.pow_succ, two_mul]; ring
  -- Then we let linarith finish
  linarith

/-- The recurence relation satisfied by Fermat numbers. -/
lemma prod_fermat (n : ℕ) : ∏ k in range n, fermat k = fermat n - 2 :=
  eq_tsub_of_add_eq $ prod_fermat_add_two _

/-- Fermat numbers are coprime.

This follows from the recurrence relations and divisibility,
as well as the parity of Fermat numbers.
-/
lemma fermat_coprime : Pairwise fun m n ↦ Coprime (fermat m) (fermat n) := by
  clear m n
  rintro m n hmn
  wlog hnm : n < m
  · exact (this hmn.symm $ hmn.lt_of_le $ not_lt.1 hnm).symm
  rw [← prod_fermat_add_two, add_coprime_iff_right (dvd_prod_of_mem _ $ mem_range.2 hnm),
    two_coprime]
  exact fermat_odd _

/-- ### 2nd proof of the infinitude of primes

Consider a sequence of prime divisors of the *Fermat numbers*,
one divisor per Fermat number.

These primes must be different: if the divisors were equal,
they would divide the coprime Fermat numbers, and yet, be prime,
which is impossible.
-/
lemma second_proof : ∃ P : ℕ → ℕ, Injective P ∧ ∀ k, (P k).Prime := by
  -- the primes are different
  -- We consider some list of prime divisors of the fermat numbers
  choose P hprime hdvd using fun n ↦ exists_prime_and_dvd (fermat_ne_one n)
  -- These prime divisors must all be different
  refine ⟨P, fun m n hmn ↦ ?_, hprime⟩
  · -- If the divisors were equal, they would divide coprime numbers,
    -- and yet, be prime, which is impossible.
    refine fermat_coprime.eq fun h ↦ ?_
    simpa [hmn, (hprime _).ne_one] using h.of_dvd (hdvd _) (hdvd _)

-- watch out for the simple `prime.ne_one`
-- that won't recognize primes in naturals.
/-- The standardised statement proven through Euclids proof-/
lemma second_proof_standardised : {n : ℕ | n.Prime}.Infinite := by
  obtain ⟨P, hinj, hprime⟩ := second_proof
  exact Set.infinite_of_injective_forall_mem hinj hprime

end Nat
