/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Prime

#align_import book.FormalBook_Ch1_InfinitudeOfPrimes_Proof1

/-!
# Six proofs of the inﬁnity of primes : Euclid's proof (first proof)

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize "Euclid's proof", the first of the six proofs.

This proof is present in the form of `nat.exists_infinite_primes` in mathlib,
and is also taught in "Mathematics in Lean".

## Structure

- `Euclid_proof` :
      Euclid's proof of the infinitude of primes,
      in the sense that for any finite set of natural numbers,
      we may find a prime not contained in it.

- `Euclid_proof_standardised` :
      Infinitude of primes in terms of `set.infinite`,
      proven with `Euclid_proof`.

-/


open Finset Nat

open scoped BigOperators

/-- ### Euclids proof of the infinitude of primes

Assume for contradiction that we may put all primes
in a finite set `s`.

Take the sucessor of the product of all primes in `s`:
- this number must have a prime divisor
- this divisor must divide the product of primes
- the divisor must divide 1

We just found a prime that divides 1: a contradiction.
-/
theorem Euclid_proof : ∀ s : Finset ℕ, ∃ p, Nat.Prime p ∧ p ∉ s :=
  by
  intro s
  by_contra! h
  set s_primes := s.filter Nat.Prime with s_primes_def
  -- Let's add a membership definition lemma to ease exposition
  have mem_s_primes : ∀ {n : ℕ}, n ∈ s_primes ↔ n.Prime :=
    by
    intro n
    rw [s_primes_def, mem_filter, and_iff_right_iff_imp]
    --simp [s_primes_def],
    --alternative to the previous line
    exact h n
  -- In order to get a prime factor from `nat.exists_prime_and_dvd`, we need:
  have condition : ∏ i in s_primes, i + 1 ≠ 1 :=
    by
    intro con
    rw [add_left_eq_self] at con
    have however : 0 < ∏ i in s_primes, i :=
      by
      apply prod_pos
      intro n ns_primes
      apply prime.pos
      exact mem_s_primes.mp ns_primes
    apply lt_irrefl 0
    nth_rw 2 [← Con]
    exact however
  obtain ⟨p, pp, pdvd⟩ := exists_prime_and_dvd condition
  -- The factor also divides the product:
  have : p ∣ ∏ i in s_primes, i := by
    apply dvd_prod_of_mem
    rw [mem_s_primes]
    apply pp
  -- Using the properties of divisibility, we reach a contradiction thorugh:
  have problem : p ∣ 1 := by
    convert dvd_sub' pdvd this
    simp only [add_tsub_cancel_left, eq_self_iff_true]
  -- via simp
  exact (Nat.Prime.not_dvd_one pp) problem

-- #check Euclid_proof
/-- The standardised statement proven through Euclids proof-/
theorem Euclid_proof_standardised : {n : ℕ | n.Prime}.Infinite :=
  by
  rw [Set.Infinite]
  intro con
  obtain ⟨p, ⟨p_prop, p_mem⟩⟩ := Euclid_proof (Set.Finite.toFinset Con)
  apply p_mem
  rw [Set.Finite.mem_toFinset Con]
  rw [Set.mem_setOf_eq]
  exact p_prop
