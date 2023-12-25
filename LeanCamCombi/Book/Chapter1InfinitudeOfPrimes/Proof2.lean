/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity

#align_import book.FormalBook_Ch1_InfinitudeOfPrimes_Proof2

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


open Finset Nat

open scoped BigOperators

/-- The Fermat numbers-/
def f : ℕ → ℕ := fun n => 2 ^ 2 ^ n + 1

/-- An evaluation lemma-/
theorem F₀ : f 0 = 3 := by
  rw [f]
  norm_num

--simp only [pow_zero, pow_one],
--alternative to the previous line
/-- A technical lemma used to show the bound 2 < F n -/
theorem fermat_stricly_monotone {n : ℕ} : f n < f n.succ :=
  by
  rw [f]
  rw [add_lt_add_iff_right]
  rw [pow_succ]
  refine' (pow_lt_pow_iff one_lt_two).mpr _
  norm_num

/-- A technical lemma used to handle subtraction of naturals,
    as well as the fact that F n ≠ 1 -/
theorem fermat_bound (n : ℕ) : 2 < f n :=
  by
  induction' n with n ih
  · rw [F₀]
    norm_num
  · exact lt_trans ih fermat_stricly_monotone

/-- Fermat numbers are odd-/
theorem fermat_odd {n : ℕ} : Odd (f n) := by
  rw [f]
  rw [Nat.odd_iff_not_even]
  rw [even_add_one]
  rw [Classical.not_not]
  rw [even_pow]
  constructor
  · exact even_two
  · exact ne_of_gt (pow_pos zero_lt_two _)

/-- The recurence relation satisfied by Fermat numbers-/
theorem fermat_product (n : ℕ) : ∏ k in range n, f k = f n - 2 :=
  by
  induction' n with n ih
  trivial
  rw [prod_range_succ]
  rw [ih]
  -- We prove a form without subtraction of naturals
  have h : f n * f n + 2 = f n.succ + 2 * f n :=
    by
    rw [f]
    dsimp
    simp only [add_mul, mul_add]
    simp only [one_mul, mul_one]
    simp only [pow_succ, two_mul]
    simp only [pow_add]
    ring
  -- Then we let linarith finish, using the identity and
  -- the following inequalities to certify subtraction isn't truncated.
  have h_natsub_1 := le_of_lt (fermat_bound n)
  have h_natsub_2 := le_of_lt (fermat_bound n.succ)
  linarith

/-- Fermat numbers are coprime.

This follows from the recurrence relations and divisibility,
as well as the parity of Fermat numbers.
-/
theorem fermat_coprimes (k n : ℕ) (h : k < n) : Coprime (f n) (f k) :=
  by
  -- Some notation and facts to ease exposition
  let m := (f n).gcd (f k)
  have h_n : m ∣ f n := (f n).gcd_dvd_left (f k)
  have h_k : m ∣ f k := (f n).gcd_dvd_right (f k)
  -- This will contradict Fermat numbers parity
  have h_m : m ∣ 2 :=
    by
    -- The gcd divides the product of Fermat numbers up n-1
    -- since it divides the kth term
    have h_m_prod : m ∣ ∏ k in range n, f k :=
      by
      apply dvd_trans h_k
      apply dvd_prod_of_mem
      rw [mem_range]; exact h
    -- This product is also found in:
    have h_prod : ∏ k in range n, f k + 2 = f n :=
      by
      rw [fermat_product]
      have h_bound := lt_trans one_lt_two (fermat_bound n)
      exact Nat.sub_add_cancel h_bound
    -- Hence we can use divisibility of linear combinations
    -- to conclude with our claim.
    refine' (Nat.dvd_add_right h_m_prod).mp _
    rw [h_prod]
    exact h_n
  have h_one_or_two := (dvd_prime prime_two).mp h_m
  cases' h_one_or_two with h_one h_two
  · exact h_one
  -- This is where the Fermat numbers parity, which we derived from
  -- their closed form, comes into play.
  · exfalso
    rw [h_two] at h_n
    have h_even : Even (f n) := even_iff_two_dvd.mpr h_n
    have h_odd : Odd (f n) := fermat_odd
    exact (even_iff_not_odd.mp h_even) h_odd

/-- A technical lemma to allow for the use of `nat.exists_prime_and_dvd`
    on Fermat numbers -/
theorem fermat_neq (n : ℕ) : f n ≠ 1 := by
  intro con
  linarith [fermat_bound n]

/-- ### 2nd proof of the infinitude of primes

Consider a sequence of prime divisors of the *Fermat numbers*,
one divisor per Fermat number.

These primes must be different: if the dividors were equal,
they would divide the coprime Fermat numbers, and yet, be prime,
which is impossible.
-/
theorem second_proof :
    ∃ P : ℕ → ℕ,
      (-- a function
        ∀ k, (P k).Prime) ∧-- with prime values
        ∀ k, ∀ q, k ≠ q → P k ≠ P q :=
  by
  -- the primes are different
  -- We consider some list of prime dividors of the fermat numbers
  let prime_dvds n := @exists_prime_and_dvd (f n) (fermat_neq n)
  obtain ⟨P, Pprop⟩ := Classical.axiom_of_choice prime_dvds
  dsimp at *; clear prime_dvds
  -- These prime dividors must all be different
  use P
  constructor
  · intro k
    exact (Pprop k).1
  · -- If the dividors were equal, they would divide coprime numbers,
    -- and yet, be prime, which is impossible.
    intro k q knq problem
    wlog C : k < q with Symmetry
    · specialize Symmetry P Pprop q k
      specialize Symmetry (Ne.symm knq)
      specialize Symmetry (Eq.symm problem)
      specialize Symmetry (lt_of_le_of_ne (not_lt.mp C) (Ne.symm knq))
      exact Symmetry
    have h_prime := (Pprop k).1
    have h_dvd_1 := (Pprop k).2
    have h_dvd_2 := (Pprop q).2
    rw [← problem] at h_dvd_2
    have promblemo := eq_one_of_dvd_coprimes (fermat_coprimes k q C) h_dvd_2 h_dvd_1
    exact (Nat.Prime.ne_one h_prime) promblemo

-- watch out for the simple `prime.ne_one`
-- that won't recognize primes in naturals.
/-- The standardised statement proven through Euclids proof-/
theorem second_proof_standardised : {n : ℕ | n.Prime}.Infinite :=
  by
  set f := Classical.choose second_proof with f_def
  have f_prop := Classical.choose_spec second_proof; rw [← f_def] at f_prop
  apply @Set.infinite_of_injective_forall_mem ℕ ℕ _ {n : ℕ | n.Prime} f
  · rw [Function.Injective]
    intro a b
    contrapose
    simp_rw [← Ne.def]
    --simple rw is not enough
    exact f_prop.2 a b
  · simp_rw [Set.mem_setOf_eq]
    exact f_prop.1
