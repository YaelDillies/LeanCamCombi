/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Combinatorics.DoubleCounting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

#align_import book.FormalBook_Ch27_PigeonholeDoublecounting_numbers_again

/-!
# Pigeon-hole and double counting : Numbers again

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 27: "Pigeon-hole and double counting".
In this file, we formalize the section "Numbers again".


## Structure

- `claim` :
      The average number of divisors of numbers from 1 to n is
      upperbounded by the harmonic sum up to n, and lowerbounded
      by its predecessor.

- `num_of_mult_le` :
      The number of multiples of `m` in 1,...,n is `n/m`.

- `main_result_pre` :
      The double counting relation linking the number of
      mulitples and the number of divisors.

- `upperbound` :
      The upperbound from the calim

- `lowerbound` :
      The lowerbound from the claim

-/


open Finset

/-- The number of multiples of `m` in 1,...,n is `n/m`.
Recall that `n/m` is the quotient of natural numbers,
which coincides with the floor of the fraction n/m.
-/
theorem num_of_mult_le (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ((Icc 1 n).filterₓ fun x => ∃ q, x = m * q).card = n / m :=
  by
  -- We rewrite it as an image so as to use `card_image_of_injective`.
  let S := (Icc 1 (n / m)).image fun x => m * x
  have RW : ((Icc 1 n).filterₓ fun x => ∃ q, x = m * q) = S :=
    by
    ext x
    constructor
    · intro xfil
      simp only [Finset.mem_image, Finset.mem_Icc, S]
      simp only [Finset.mem_Icc, Finset.mem_filter] at xfil
      rcases xfil with ⟨⟨lbound, ubound⟩, ⟨q, xmul⟩⟩
      use q
      constructor; constructor
      · by_contra! K
        rw [Nat.lt_one_iff] at K
        rw [K] at xmul
        rw [MulZeroClass.mul_zero] at xmul
        linarith
      · rw [xmul] at ubound
        rw [mul_comm] at ubound
        rw [← Nat.le_div_iff_mul_le] at ubound
        exact ubound
        exact Nat.pos_of_ne_zero hm
      · exact xmul.symm
    · intro xS
      simp only [S, Finset.mem_image, Finset.mem_filter] at *
      rcases xS with ⟨q, qIcc, xmul⟩
      rw [mem_Icc] at *
      cases' qIcc with lbound ubound
      constructor; constructor
      · rw [← xmul]
        rw [← one_mul 1]
        apply Nat.mul_le_mul
        exact nat.one_le_iff_ne_zero.mpr hm
        exact lbound
      · rw [← xmul]
        rw [mul_comm]
        rw [← Nat.le_div_iff_mul_le]
        exact ubound
        exact Nat.pos_of_ne_zero hm
      · use q
        exact xmul.symm
  rw [RW]
  dsimp [S]
  rw [card_image_of_injective _]
  -- Handled by a simp ; the main theorem is `nat.card_Icc` .
  simp only [Nat.add_succ_sub_one, add_zero, Nat.card_Icc, eq_self_iff_true]
  rw [Function.Injective]
  intro a b eq
  rw [mul_eq_mul_left_iff] at eq
  cases Eq
  exact Eq
  exfalso
  exact hm Eq

/-- Expressing the mulitples of `m` in the fromework of
`finset.bipartite_above`, for double counting.
-/
theorem mult_rel (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    bipartiteAbove (fun a b => a ∣ b) (Icc 1 n) m = (Icc 1 n).filterₓ fun x => ∃ q, x = m * q :=
  by
  simp only [Finset.bipartiteAbove]
  congr

/-- Expressing the divisors of `m` in the fromework of
`finset.bipartite_below`, for double counting.
-/
theorem dvd_rel (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    bipartiteBelow (fun a b => a ∣ b) (Icc 1 n) m = (Icc 1 n).filterₓ fun x => ∃ q, m = x * q :=
  by
  simp only [Finset.bipartiteBelow]
  congr

open scoped BigOperators

/-- The double counting relation linking the number of mulitples and
the number of divisors. The double counting principle is implemented as
`sum_card_bipartite_above_eq_sum_card_bipartite_below`.
-/
theorem main_result_pre (n : ℕ) (hn : n ≠ 0) :
    ∑ m in Icc 1 n, ((Icc 1 n).filterₓ fun x => ∃ q, x = m * q).card =
      ∑ m in Icc 1 n, ((Icc 1 n).filterₓ fun x => ∃ q, m = x * q).card :=
  by apply sum_card_bipartite_above_eq_sum_card_bipartite_below

-- Note: there was no use of `mult_rel` and `dvd_rel`.
-- If one deletes them, this still proof still works!
/-- We now have an explicit expression for
the sum of the number of divisors.
-/
theorem main_result_pre_rw (n : ℕ) (hn : n ≠ 0) :
    ∑ m in Icc 1 n, ((Icc 1 n).filterₓ fun x => ∃ q, m = x * q).card = ∑ m in Icc 1 n, n / m :=
  by
  rw [(main_result_pre n hn).symm]
  apply sum_congr
  rfl
  intro m mdef
  replace mdef : m ≠ 0 := by
    rw [mem_Icc] at mdef
    linarith
  exact num_of_mult_le n m hn mdef

/-- We cast the explicit expression for
the sum of the number of divisors
to ℚ, so as to take averages, using
fractions.
-/
theorem main_result_pre_cast (n : ℕ) (hn : n ≠ 0) :
    ∑ m in Icc 1 n, ((n / m : ℕ) : ℚ) =
      (∑ m in Icc 1 n, ((Icc 1 n).filterₓ fun x => ∃ q, m = x * q).card : ℚ) :=
  by
  have := main_result_pre_rw n hn
  rw [← @Nat.cast_inj ℚ _ _] at this
  push_cast at this
  rwa [eq_comm]

/-- We upper bound the average number of multiples of a number
in [n] by the harmonic sum.
-/
theorem upperbound (n : ℕ)
    (hn : n ≠ 0) :-- To keep `/` as a quotient of two naturals,
        -- we use `((n/m : ℕ): ℚ))`
        (1 / n : ℚ) *
        ∑ m in Icc 1 n, ((n / m : ℕ) : ℚ) ≤
      ∑ m in Icc 1 n, (1 / m : ℚ) :=
  by
  -- Here, `(1/m : ℚ)` is interpreted as a fraction
  rw [mul_sum]
  apply sum_le_sum
  intro i idef
  have : 0 < (n : ℚ) := by
    apply lt_of_le_of_ne
    exact Nat.cast_nonneg n
    rw [ne_comm]
    rw [Nat.cast_ne_zero]
    exact hn
  apply le_of_mul_le_mul_left _ this
  clear this
  rw [← mul_assoc]
  rw [show (n : ℚ) * (1 / n : ℚ) = (1 : ℚ)
      by
      apply mul_one_div_cancel
      rw [Nat.cast_ne_zero]
      exact hn]
  rw [one_mul]
  rw [mul_one_div]
  exact Nat.cast_div_le

/-- This is the inequality `x-1 ≤ ⌊x⌋` in our context.
-/
theorem lb_pre (n m : ℕ) (hm : m ≠ 0) : (n / m : ℚ) - 1 ≤ ((n / m : ℕ) : ℚ) :=
  by
  have : 0 < (m : ℚ) := by
    rw [Nat.cast_pos]
    exact Nat.pos_of_ne_zero hm
  apply le_of_mul_le_mul_left _ this
  clear this
  rw [mul_sub, mul_one]
  rw [show (m : ℚ) * (n / m : ℚ) = (n : ℚ)
      by
      apply mul_div_cancel'
      intro con
      rw [show (0 : ℚ) = ↑(0 : ℕ) by simp only [algebraMap.coe_zero, eq_self_iff_true]] at con
      rw [Nat.cast_inj] at con
      exact hm Con]
  rw [show (m : ℚ) * ↑(n / m : ℕ) = ↑(m * (n / m : ℕ)) by
      simp only [mul_eq_mul_left_iff, true_or_iff, eq_self_iff_true, Nat.cast_inj, Nat.cast_eq_zero,
        Nat.cast_mul]]
  rw [show m * (n / m) = n - n % m by
      rw [eq_comm]
      rw [Nat.sub_eq_iff_eq_add _]
      rw [eq_comm, add_comm]
      apply Nat.mod_add_div
      apply Nat.mod_le]
  rw [Nat.cast_sub (Nat.mod_le n m)]
  apply sub_le_sub
  simp only [le_refl, Nat.cast_le]
  apply le_of_lt
  rw [Nat.cast_lt]
  apply Nat.mod_lt
  exact Nat.pos_of_ne_zero hm

/-- A rewrite we singled out to shorten the proof of `lowerbound`
-/
theorem last_rw (n x : ℕ) (hn : n ≠ 0) : (1 / n : ℚ) * (↑n / ↑x - 1) = 1 / ↑x - 1 / ↑n :=
  by
  --note : x≠0 not needed ; consider the check and eval that follow
  rw [mul_sub, mul_one]
  simp only [one_div, sub_left_inj]
  ring_nf
  rw [mul_assoc]
  rw [show (n : ℚ) * (↑n)⁻¹ = 1 by
      apply mul_inv_cancel
      rw [Nat.cast_ne_zero]
      exact hn]
  rw [mul_one]

-- #check (1 : ℚ)/(0 : ℚ)
#eval (1 : ℚ) / (0 : ℚ)

/-- We lower bound the average by the harmonic series
-/
theorem lowerbound (n : ℕ) (hn : n ≠ 0) :
    ∑ m in Icc 1 n, (1 / m : ℚ) - 1 ≤ (1 / n : ℚ) * ∑ m in Icc 1 n, ((n / m : ℕ) : ℚ) :=
  by
  -- We use `x-1 ≤ ⌊x⌋` in the terms of the sum
  have pre : ∑ m in Icc 1 n, ((n / m : ℚ) - 1) ≤ ∑ m in Icc 1 n, ((n / m : ℕ) : ℚ) :=
    by
    apply sum_le_sum
    intro i idef
    have : i ≠ 0 := by
      rw [mem_Icc] at idef
      linarith
    exact lb_pre n i this
  -- We take the average as follows:
  have tec : Monotone fun x => (1 / n : ℚ) * x :=
    by
    dsimp [Monotone]
    intro a b ineq
    apply mul_le_mul_of_nonneg_left ineq
    simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  apply_fun fun x => (1 / n : ℚ) * x at pre  using tec
  clear tec
  -- Now come the algebraic rewrites
  rw [mul_sum] at pre
  simp_rw [last_rw n _ hn] at pre
  rw [sum_sub_distrib] at pre
  rw [sum_const] at pre
  rw [Nat.card_Icc, Nat.add_sub_cancel] at pre
  simp only [one_div, algebraMap.coe_one, nsmul_eq_mul, Nat.cast_add, Finset.sum_congr] at pre
  -- technique use simp look at the simp only [] and delete the undesired simplifcations from the list
  simp only [one_div, algebraMap.coe_one, nsmul_eq_mul, Nat.cast_add, Finset.sum_congr]
  rw [show (n : ℚ) * (↑n)⁻¹ = 1 by
      apply mul_inv_cancel
      rw [Nat.cast_ne_zero]
      exact hn] at
    pre
  exact pre

/-- The average number of divisors of numbers from 1 to n is
upperbounded by the harmonic sum up to n, and lowerbounded
by its predecessor.
-/
theorem claim (n : ℕ) (hn : n ≠ 0) :
    ∑ m in Icc 1 n, (1 / m : ℚ) - 1 ≤
        (1 / n : ℚ) * (∑ m in Icc 1 n, ((Icc 1 n).filterₓ fun x => ∃ q, m = x * q).card : ℚ) ∧
      (1 / n : ℚ) * (∑ m in Icc 1 n, ((Icc 1 n).filterₓ fun x => ∃ q, m = x * q).card : ℚ) ≤
        ∑ m in Icc 1 n, (1 / m : ℚ) :=
  by
  rw [← main_result_pre_cast n hn]
  constructor
  exact lowerbound n hn
  exact upperbound n hn
