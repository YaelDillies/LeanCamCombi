/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Gcd.Basic
import Mathlib.Data.Nat.Parity

/-!
# Pigeon-hole and double counting : Numbers

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 27: "Pigeon-hole and double counting".
In this file, we formalize the section "Numbers".


## Structure

- `claim_1` :
      In any `A ⊆ {1, 2, . . . , 2n}` of size `n+1`,
      we may find two distinct coprime numbers.
- `claim_2` :
      In any `A ⊆ {1, 2, . . . , 2n}` of size `n+1`,
      we may find two distinct numbers so that
      one divides the other.

-/

open Finset

-- ### Claim 1
/-- The fact that a number and its successor, sated in
a form particularly well suited for for the proof
of `claim_1`.

Library search didn't point me to a possible
mathlib version of this result.
-/
theorem succ_coprime (n m : Nat) (h : n = m + 1) : Nat.Coprime n m := by
  rw [h]
  rw [Nat.coprime_self_add_left]
  exact Nat.coprime_one_left m

/-- ### 1st claim

In any `A ⊆ {1, 2, . . . , 2n}` of size `n+1`,
we may find two distinct coprime numbers.
-/
theorem claim_1 (n : Nat) (h : 1 ≤ n) (A : Finset ℕ)
    (Adef : A ∈ powersetCard (n + 1) (Icc 1 (2 * n))) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ Nat.Coprime a b := by
  rw [mem_powerset_len] at Adef
  /-
    This will follow from `succ_coprime` once we find
    a pair of successors in A.
    For this purpose, we group elements as {1,2}, {3,4}, etc.
    A function achieving this grouping is `(λ (x : ℕ), (x+1) / 2)`
    -/
  have Lem1 :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ (fun x : ℕ => (x + 1) / 2) a = (fun x : ℕ => (x + 1) / 2) b := by
    let group_fn x := (x + 1) / 2
    -- A condition to apply `exists_ne_map_eq_of_card_lt_of_maps_to`
    have map_condition : ∀ a, a ∈ A → group_fn a ∈ Icc 1 n := by
      intro x xdef
      dsimp [group_fn]
      replace xdef := Adef.1 xdef
      rw [mem_Icc] at *
      constructor
      · rw [Nat.le_div_iff_mul_le]
        linarith
        norm_num
      · rw [Nat.div_le_iff_le_mul_add_pred]
        linarith
        norm_num
    apply exists_ne_map_eq_of_card_lt_of_maps_to _ map_condition
    -- this is the pigeonhole principle
    -- We're left to show the condition on the sizes
    rw [Nat.card_Icc]
    simp only [add_tsub_cancel_right]
    rw [Adef.2]
    --apply nat.lt_succ, -- but `nat.le_succ` is a thing
    simp only [lt_add_iff_pos_right, eq_self_iff_true, Nat.lt_one_iff]
  rcases Lem1 with ⟨a, aA, b, bA, anb, abeq⟩
  dsimp at abeq
  use a; constructor; use aA
  use b; constructor; use bA
  constructor; exact anb
  -- To determine which of a and b is the successor,
  -- we investigate the remainders
  have Lem2 : (a + 1) % 2 ≠ (b + 1) % 2 := by
    intro con
    have : a + 1 = b + 1 := by
      rw [← Nat.div_add_mod (a + 1) 2]
      rw [← Nat.div_add_mod (b + 1) 2]
      -- cc, -- works, but too slow
      rw [abeq, Con]
    apply anb
    exact Nat.add_right_cancel this
  -- We may order the remainders wlog
  wlog H : (a + 1) % 2 < (b + 1) % 2 with Sym
  · push_neg at H
    rw [ne_comm] at *
    rw [eq_comm] at abeq
    replace H := lt_of_le_of_ne H Lem2
    specialize Sym n h A Adef
    specialize Sym b bA a aA anb abeq Lem2 H
    rw [Nat.coprime_comm]
    exact Sym
  -- Next, we go over the possibilities for (b+1)%2
  have := Nat.mod_lt (b + 1) (show 0 < 2 by norm_num)
  interval_cases bcase : (b + 1) % 2
  · exfalso
    rw [bcase] at H
    exact (Nat.not_lt_zero _) H
  · rw [bcase] at H
    rw [Nat.lt_one_iff] at H
    rw [Nat.coprime_comm]
    apply succ_coprime b a
    -- we may now put out plan to action
    apply @Nat.add_right_cancel _ 1 _
    rw [← Nat.div_add_mod (a + 1) 2]
    rw [← Nat.div_add_mod (b + 1) 2]
    rw [abeq, bcase, H]
    norm_num

-- ### Claim 2
/-- A technical calculation showing `2*n < 2^(n+1)` -/
theorem ineq_tec (n : ℕ) : 2 * n < 2 ^ (n + 1) := by
  induction' n with n ih
  ·
    simp only [Nat.zero_eq, eq_self_iff_true, pow_one, zero_lt_bit0, zero_add, Nat.lt_one_iff,
      MulZeroClass.mul_zero]
  rw [Nat.succ_eq_add_one]
  rw [pow_add]
  rw [mul_add]
  rw [pow_one]
  rw [mul_one]
  rw [mul_two]
  nth_rw 2 [← pow_one 2]
  have : 2 ^ 1 ≤ 2 ^ (n + 1) := by apply pow_le_pow_right; norm_num; linarith
  exact add_lt_add_of_lt_of_le ih this

/-- Every number in `{1, 2, . . . , 2n}` may be written as `(2^k)*m`
for an *odd* `m` in `{1, 2, . . . , 2n}`.
-/
theorem decompo_lemma (n a : ℕ) (aR : a ∈ Icc 1 (2 * n)) :
    ∃ m k : ℕ, a = 2 ^ k * m ∧ m ∈ (Icc 1 (2 * n)).filter fun x => x % 2 = 1 := by
  /-
    The basic idea would be to use the prime factorisation of `a`,
    so that `k` would be its valuation for `2`.
    I wasn't aware for `data.nat.factorisation` when writing this.
    Also, the characterisation of valuation as a maximum I use
    turned out to be well suited to show tha `m` is odd.
    -/
  -- We define the powers of `2` that divide `a`
  let facSet := (range (n + 1)).filter fun q => ∃ p, a = 2 ^ q * p
  have facSet_nonempty : facSet.nonempty := by
    dsimp [facSet]
    rw [filter_nonempty_iff]
    use 0
    constructor
    · simp only [eq_self_iff_true, or_true_iff, Nat.lt_one_iff, Finset.mem_range, add_pos_iff]
    use a
    simp only [one_mul, eq_self_iff_true, pow_zero]
  let k := Finset.max' facSet facSet_nonempty
  have l1 : k ∈ facSet := by
    dsimp [k]
    exact Finset.max'_mem facSet facSet_nonempty
  dsimp [facSet] at l1
  rw [mem_filter] at l1
  cases' l1.2 with m eq
  -- We use the rest of the factorisation for `m`
  use m
  -- We use the maximum such power for `k`
  use k
  constructor
  exact Eq
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor; constructor
  · by_contra! con
    rw [Nat.lt_one_iff] at con
    rw [Con] at eq
    rw [MulZeroClass.mul_zero] at eq
    rw [Eq] at aR
    simp only [Nat.one_ne_zero, Finset.mem_Icc, zero_le', le_zero_iff, false_and_iff] at aR
    exact aR
  · rw [mem_Icc] at aR
    apply le_trans _ aR.2
    rw [Eq]
    apply Nat.le_mul_of_pos_left
    apply lt_of_lt_of_le Nat.zero_lt_one
    apply Nat.one_le_pow
    norm_num
  -- We now show that the rest of the factorisation is odd,
  -- as if it had more 2's, we'd contradict maximality of `k`.
  by_contra! con
  rw [Nat.mod_two_ne_one] at con
  rw [← Nat.even_iff, even_iff_two_dvd] at con
  cases' Con with q qdef
  rw [qdef] at eq
  rw [← mul_assoc] at eq
  nth_rw 2 [← pow_one 2] at eq
  rw [← pow_add] at eq
  have problem : k + 1 ∈ facSet := by
    dsimp [facSet]
    rw [mem_filter]
    constructor
    · rw [mem_range]
      by_contra! con
      rw [mem_Icc] at aR
      apply not_le_of_lt (ineq_tec n)
      apply le_trans _ aR.2
      rw [Eq]
      rw [← mul_one (2 ^ (n + 1))]
      apply Nat.mul_le_mul
      · apply pow_le_pow_right
        norm_num
        exact Con
      · by_contra! con
        rw [Nat.lt_one_iff] at con
        rw [Con] at eq
        rw [MulZeroClass.mul_zero] at eq
        rw [Eq] at aR
        exact (not_le_of_lt Nat.zero_lt_one) aR.1
    · use q
      exact Eq
  · have := le_max' facSet (k + 1) problem
    --replace raises error
    dsimp [k] at this
    apply (Nat.not_succ_le_self _) this

/-- There are `n` odd numbers in `{1, 2, . . . , 2n}`-/
theorem size_lemma (n : Nat) : ((Icc 1 (2 * n)).filter fun x => x % 2 = 1).card = n := by
  -- We use a bijection from 0,...,n-1 to the set: `(λ x xn, (2*x)+1)`.
  apply card_eq_of_bijective fun x xn => 2 * x + 1
  -- surjectivity
  · intro a aOR
    simp only [Finset.mem_Icc, Finset.mem_filter] at aOR
    rcases aOR with ⟨⟨a1, an⟩, aodd⟩
    use a / 2
    constructor
    -- `split` to introduce ∃ goals
    dsimp
    convert Nat.div_add_mod a 2
    exact aodd.symm
    rw [Nat.div_lt_iff_lt_mul _]
    rw [mul_comm]
    apply lt_of_le_of_ne an
    intro con
    rw [Con] at aodd
    rw [Nat.mul_mod_right 2 n] at aodd
    exact zero_ne_one aodd
    norm_num
  -- map
  · intro i iln
    simp only [mem_filter, mem_Icc]
    constructor; constructor
    exact le_add_self
    rw [← Nat.lt_iff_add_one_le]
    apply Nat.mul_lt_mul_of_pos_left iln
    norm_num
    rw [Nat.add_mod]
    rw [Nat.mul_mod_right 2 i]
    norm_num
  -- injectivity
  · intro i j idef jdef eq
    simp only [Nat.one_ne_zero, add_left_inj, mul_eq_mul_left_iff, or_false_iff, bit0_eq_zero] at eq
    exact Eq

open scoped Classical

-- to use `nat.find`
/-- ### 2nd claim

In any `A ⊆ {1, 2, . . . , 2n}` of size `n+1`,
we may find two distinct numbers so that
one divides the other.
-/
theorem claim_2 (n : Nat) (hn : 1 ≤ n) (A : Finset ℕ)
    (Adef : A ∈ powersetCard (n + 1) (Icc 1 (2 * n))) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a ∣ b := by
  rw [mem_powerset_len] at Adef
  -- The pigeon-map returns the `m` of the decomposition for numbers
  -- in the domain set, and 0 otherwise
  let f := fun x : Nat => if h : x ∈ Icc 1 (2 * n) then Nat.find (decompo_lemma n x h) else 0
  have cond_size : ((Icc 1 (2 * n)).filter fun x => x % 2 = 1).card < A.card := by
    rw [size_lemma]
    rw [Adef.2]
    exact lt_add_one n
  have cond_map : ∀ a, a ∈ A → f a ∈ (Icc 1 (2 * n)).filter fun x => x % 2 = 1 := by
    intro a aA
    dsimp [f]
    rw [dif_pos _]
    swap
    exact Adef.1 aA
    have := Nat.find_spec (decompo_lemma n a (Adef.1 aA))
    rcases this with ⟨k, kdef, eq⟩
    exact Eq
  obtain
    ⟨a, adef, b, bdef, anb, abprop⟩ :=--we use the pigeonhole principle
      exists_ne_map_eq_of_card_lt_of_maps_to
      cond_size cond_map
  dsimp [f] at abprop
  rw [dif_pos (Adef.1 adef)] at abprop
  rw [dif_pos (Adef.1 bdef)] at abprop
  obtain ⟨ka, ka_def, ka_eq⟩ := Nat.find_spec (decompo_lemma n a (Adef.1 adef))
  obtain ⟨kb, kb_def, kb_eq⟩ := Nat.find_spec (decompo_lemma n b (Adef.1 bdef))
  -- We have to disjoin cases on which of `a,b` divides the other,
  -- which dependes on their valuation in 2.
  -- wlog H : ka ≤ kb with Sym, --hmm
  by_cases q : ka ≤ kb
  · use a; use adef; use b; use bdef
    constructor
    exact anb
    use 2 ^ (kb - ka)
    rw [ka_def, kb_def]
    rw [mul_assoc]
    nth_rw_rhs 2 [mul_comm]
    rw [← mul_assoc]
    rw [← pow_add]
    -- rw add_sub_cancel'_right, -- we're not in a group
    rw [← Nat.add_sub_assoc q]
    rw [Nat.add_sub_cancel_left]
    rw [abprop]
  · push_neg at q
    use b; use bdef; use a; use adef
    constructor
    rw [ne_comm] at anb
    exact anb
    use 2 ^ (ka - kb)
    rw [ka_def, kb_def]
    rw [mul_assoc]
    nth_rw_rhs 2 [mul_comm]
    rw [← mul_assoc]
    rw [← pow_add]
    -- rw add_sub_cancel'_right, -- we're not in a group
    rw [← Nat.add_sub_assoc (le_of_lt q)]
    rw [Nat.add_sub_cancel_left]
    rw [abprop]
