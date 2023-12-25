/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathbin.Tactic.Default

/-!
# Pigeon-hole and double counting : Sums

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 27: "Pigeon-hole and double counting".
In this file, we formalize the section "Sums".


## Structure

- `exists_subseq_sum_eq_zero` :
      Suppose we are given the n first terms of an integer
      sequence `a`, which need not be pairwise distinct.
      Then there is always a set of consecutive numbers
      k+1,k+2,...,l in [0,n], whose sum of the corresponding
      terms of `a` is a multiple of n.

-/


open Finset

/-- A technical lemma for algebraic manipulations with `int.nat_mod`.
-/
theorem tec_mod (n : ℕ) (hn : n ≠ 0) (a b : ℤ) (H : Int.natMod a n = Int.natMod b n) :
    (Int.natMod (a - b) n : ℤ) = 0 := by
  simp only [Int.natMod] at *
  apply_fun fun x => (x : ℤ) at H
  have rw_main : ∀ c : ℤ, ↑(c % ↑n).toNat = c % ↑n := by
    intro c
    apply Int.toNat_of_nonneg
    apply Int.emod_nonneg
    simp only [Ne.def, Nat.cast_eq_zero]
    exact hn
  rw [rw_main a] at H
  rw [rw_main b] at H
  rw [rw_main (a - b)]
  rw [Int.sub_emod]
  rw [H]
  simp only [sub_self]
  exact (n : ℤ).zero_mod

open scoped BigOperators

/-- A technical lemma for deleting the first terms of a sum
indexed by `Icc`, all interms of `Icc`.
-/
theorem tec_sum (a : ℕ → ℤ) (b c : ℕ) (h : b < c) :
    ∑ i : ℕ in Icc 1 c, a i - ∑ i : ℕ in Icc 1 b, a i = ∑ i : ℕ in Icc (b + 1) c, a i := by
  have decompo :
    Icc 1 c =
      disj_union (Icc (b + 1) c) (Icc 1 b)
        (by
          rw [disjoint_iff_inter_eq_empty]
          ext y
          simp only [and_imp, Finset.not_mem_empty, Finset.mem_Icc, not_and, iff_false_iff,
            Finset.mem_inter]
          intro yes no nope
          linarith) := by
    simp only [Finset.disjUnion_eq_union]
    --library_search, --fails
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    rintro ⟨x1, xc⟩
    by_cases q : x ≤ b
    right
    exact ⟨x1, q⟩
    left
    constructor
    rw [Nat.add_one_le_iff]
    exact lt_of_not_le q
    exact xc
    intro tmp
    cases' tmp with up down
    constructor
    linarith
    exact up.2
    constructor
    exact down.1
    linarith
  rw [decompo]
  rw [Finset.sum_disjUnion]
  simp only [eq_self_iff_true, add_tsub_cancel_right]

/-- ### Claim

Suppose we are given the n first terms of an integer
sequence `a`, which need not be pairwise distinct.
Then there is always a set of consecutive numbers
k+1,k+2,...,l in [0,n], whose sum of the corresponding
terms of `a` is a multiple of n.
-/
theorem exists_subseq_sum_eq_zero (n : ℕ) (hn : n ≠ 0) (a : ℕ → ℤ) :
    ∃ k l, k ∈ range (n + 1) ∧ l ∈ range (n + 1) ∧ k < l ∧ (n : ℤ) ∣ ∑ i in Icc (k + 1) l, a i := by
  -- The pigeonhole map and the conditions
  let f m := Int.natMod (∑ i in Icc 1 m, a i) n
  have map_cond : ∀ s, s ∈ range (n + 1) → f s ∈ range n := by
    intro m mdef
    simp only [f, Finset.mem_range]
    apply Int.natMod_lt
    exact hn
  have card_cond : (range n).card < (range (n + 1)).card := by
    rw [card_range, card_range]
    linarith
  -- We apply the principle
  obtain ⟨b, bS, c, cS, anb, fbfc⟩ := exists_ne_map_eq_of_card_lt_of_maps_to card_cond map_cond
  dsimp [f] at fbfc
  -- wlog H : b < c with nam, --fails
  apply ltByCases b c
  · intro blc
    use b; use c
    constructor
    exact bS
    constructor
    exact cS
    constructor
    exact blc
    -- Some rewrites
    have to_dvd : (((Icc 1 c).Sum a - (Icc 1 b).Sum a).natMod ↑n : ℤ) = 0 := by
      apply tec_mod n hn
      exact fbfc.symm
    simp only [Int.natMod] at to_dvd
    have :
      ↑(((Icc 1 c).Sum a - (Icc 1 b).Sum a) % ↑n).toNat =
        ((Icc 1 c).Sum a - (Icc 1 b).Sum a) % ↑n := by
      apply Int.toNat_of_nonneg
      apply Int.emod_nonneg
      simp only [Ne.def, Nat.cast_eq_zero]
      exact hn
    rw [this] at to_dvd
    clear this
    rw [tec_sum a b c blc] at to_dvd
    exact Int.dvd_of_emod_eq_zero to_dvd
  -- The false case
  · intro nope
    exfalso
    exact anb nope
  -- swap b and c, proceed as in the first bloc
  · intro blc
    use c; use b
    constructor
    exact cS
    constructor
    exact bS
    constructor
    exact blc
    -- Some rewrites
    have to_dvd : (((Icc 1 b).Sum a - (Icc 1 c).Sum a).natMod ↑n : ℤ) = 0 := by
      apply tec_mod n hn
      exact fbfc
    simp only [Int.natMod] at to_dvd
    have :
      ↑(((Icc 1 b).Sum a - (Icc 1 c).Sum a) % ↑n).toNat =
        ((Icc 1 b).Sum a - (Icc 1 c).Sum a) % ↑n := by
      apply Int.toNat_of_nonneg
      apply Int.emod_nonneg
      simp only [Ne.def, Nat.cast_eq_zero]
      exact hn
    rw [this] at to_dvd
    clear this
    rw [tec_sum a c b blc] at to_dvd
    exact Int.dvd_of_emod_eq_zero to_dvd
