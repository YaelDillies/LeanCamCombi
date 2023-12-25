import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.PrimeNormNum
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Six proofs of the inﬁnity of primes : 4th proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize "Fourth proof", the 4th of the six proofs.


## Structure

- `fourth_proof` :
      The fourth proof of infinitude of primes.
      It's based on the divergence of the harmonic series.
- `π` :
      The prime counting function
- `the_great_merger` :
      We lower bound the prime counting function by the
      harmonic series. This is the central argument for
      showing infinitude of primes.
- `order_the_prod` :
      Ordering the product `∏ (p/(p-1) : ℚ)` according
      to the order of increasing primes
- `kth_prime_among_bound` :
      Shows that the kth prime is ≥ k+1
- `prod_ordered_primes_bound` :
      Lower-bounds (π n)+1 by the ordered product of primes
- `prod_sum_bound` :
      Lower-bounds the product of primes by the product
      of geometric sums over the primes.
- `the_great_split_part_1` :
      First step in linking the hamronic series to the
      produc of geometric sums:
      distributing the product of sums.
- `the_great_split_part_2` :
      Second step in linking the hamronic series to the
      produc of geometric sums:
      lower-bounding the distributing the product of sums
      by the sum on the subset obtained by filtering out
      the terms who's value isn a 1/k for k∈[n].
- `the_great_split_part_3` :
      Final step in linking the hamronic series to the
      produc of geometric sums:
      upper-bound the harmonic sum with the filtered
      sum of products.
- `quick_prime_decompo` :
      A home-made version of decomposition into primes.
- `harmonic_unbounded` :
      A home-made proof that the harmonic series is unbounded.
-/


/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
-- Imports not essential to the file, only used for
-- Imports not essential to the file, only used for
-- allusions to alternative formalizations.
-- allusions to alternative formalizations.
open Finset

open scoped BigOperators

/-- The set of primes `≤ n`-/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun p => Nat.Prime p

/-- Counts the number of primes `≤ n`-/
def π (n : ℕ) : ℕ :=
  ((range (n + 1)).filter fun p => Nat.Prime p).card

-- They are computable
#eval π 10

#eval π 100000

-- first 0 where this made my laptop take a second,
-- next 0 causes a timeout
#eval primesUpTo 10

#eval primesUpTo 100000

-- I later found out about:
-- #check nat.nth
--However, it's not computable. Making the following
-- and #eval will fail
-- #check nat.nth nat.prime 3
/-- A function that takes as input `n`, `k` and a proof that
`k < (π n)`, and returns the `k`th prime among the first
`n+1` numbers 0,1,...,n.

We start the counting at 0 for `k`.
-/
def kthPrimeAmong (n k : ℕ) (h : k < π n) :=
  List.nthLe (Finset.sort (· ≤ ·) ((range (n + 1)).filter fun p => Nat.Prime p)) k
    (by rw [π] at h ; simp only [Finset.length_sort]; exact h)

/-
For some functions, specific value equalities can be
shown with refl, dec_trivial, or norm_num.
For example:
-/
def funtest (x : Nat) : ℕ :=
  2 * x

#eval funtest 2

example : funtest 2 = 4 := by rfl

/-
For more complicated ones, proofs are necessary.
The following proof is due to Bhavik Mehta.
-/
theorem thanks_Bhavik : π 10 = 4 := by
  rw [π]
  iterate 11

    rw [Finset.range_succ, Finset.filter_insert, apply_ite Finset.card,
      Finset.card_insert_of_not_mem]
    swap; · simp
    norm_num1
    simp only [if_true, if_false]
  rw [Finset.range_zero, Finset.filter_empty, Finset.card_empty]
  norm_num1

-- This computes the 2nd prime in 0,1,...10
#eval kthPrimeAmong 10 1 (by rw [thanks_Bhavik]; norm_num)

-- This computes the 4th prime in 0,1,...10
#eval kthPrimeAmong 10 3 (by rw [thanks_Bhavik]; norm_num)

/-- A function that takes as input `n`, `p` and a proof that
`p` is a prime `≤ n` in the language of finsets,
and returns the rank/order of the prime `p`,
in the form of a number of type ` fin (π n)`.

We start the counting at 0 for the rank/order.
-/
def primeRankAmong (n p : ℕ) (h : p ∈ (range (n + 1)).filter fun q => Nat.Prime q) : Fin (π n) :=
  ⟨List.indexOf p (Finset.sort (· ≤ ·) ((range (n + 1)).filter fun q => Nat.Prime q)), by
    simp only [π]; rw [← Finset.length_sort LE.le]
    rw [List.indexOf_lt_length]; rw [Finset.mem_sort]; exact h⟩

-- This computes the rank of the prime 5 in 0,1,...10,
-- which is 3.
#eval primeRankAmong 10 5 (by norm_num)

-- This computes the rank of the prime 5 in 0,1,...10,
-- which is 4.
#eval primeRankAmong 10 7 (by norm_num)

/-- `kth_prime_among` is a left inverse to `prime_rank_among` -/
theorem order_tec_1 (n p : ℕ) (h : p ∈ (range (n + 1)).filter fun q => Nat.Prime q) :
    kthPrimeAmong n (primeRankAmong n p h).val (primeRankAmong n p h).Prop = p := by
  simp [kthPrimeAmong, primeRankAmong]

/-- `kth_prime_among n k h` is a prime `≤ n` -/
theorem kthPrimeAmong_makes_sense (n k : ℕ) (h : k < π n) :
    kthPrimeAmong n k h ∈ (range (n + 1)).filter Nat.Prime := by
  rw [kthPrimeAmong]
  rw [← Finset.mem_toList]
  have :
    List.Perm (Finset.sort (· ≤ ·) (Filter Nat.Prime (range (n + 1))))
      (Filter Nat.Prime (range (n + 1))).toList :=
    sort_perm_to_list LE.le (Filter Nat.Prime (range (n + 1)))
  rw [← List.Perm.mem_iff this]
  apply List.nthLe_mem

/-- `kth_prime_among n k h` is a prime `≤ n`, explicit version -/
theorem kthPrimeAmong_makes_sense' (n k : ℕ) (h : k < π n) :
    kthPrimeAmong n k h < n + 1 ∧ Nat.Prime (kthPrimeAmong n k h) := by
  have := kthPrimeAmong_makes_sense n k h
  rw [mem_filter] at this
  rwa [mem_range] at this

/-- `kth_prime_among` is a right inverse to `prime_rank_among` -/
theorem order_tec_2 (n k : ℕ) (h : k < π n) :
    primeRankAmong n (kthPrimeAmong n k h) (kthPrimeAmong_makes_sense n k h) = ⟨k, h⟩ := by
  simp [kthPrimeAmong, primeRankAmong]

/-- Expressing the set of primes `≤ n` as the image of
0,1,...,(π n)-1 under `kth_prime_among`.
-/
theorem tec_order_set {n : ℕ} :
    ((range (n + 1)).filter fun p => Nat.Prime p) =
      image (fun k : Fin (π n) => kthPrimeAmong n k.val k.Prop) (univ : Finset (Fin (π n))) := by
  ext x
  constructor
  · intro xfil
    rw [mem_image]
    use primeRankAmong n x xfil
    simp only [true_and_iff, Finset.mem_univ, Fin.val_eq_coe]
    apply order_tec_1
  · intro xim
    simp at xim
    cases' xim with y ydef
    rw [← ydef]
    apply kthPrimeAmong_makes_sense

/-- Ordering `∏ (p/(p-1) : ℚ)` according to the order of primes,
using `kth_prime_among`.
-/
theorem order_the_prod {n : ℕ} :
    ∏ p in (range (n + 1)).filter fun p => Nat.Prime p, (p / (p - 1) : ℚ) =
      ∏ k in (univ : Finset (Fin (π n))),
        (kthPrimeAmong n k.val k.Prop / (kthPrimeAmong n k.val k.Prop - 1) : ℚ) := by
  rw [tec_order_set]
  apply prod_image
  simp
  intro x y eq
  rw [kthPrimeAmong] at eq
  apply Fin.eq_of_veq
  have : List.Nodup (Finset.sort (· ≤ ·) ((range (n + 1)).filter fun p => Nat.Prime p)) :=
    sort_nodup LE.le (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)))
  apply list.nodup_iff_nth_le_inj.mp this
  exact Eq

-- We didn't end up needing the following
/-- `π` is an increasing function that increases either by 0
or by one for each successive number `n`.
-/
theorem π_increase {n : ℕ} : π n ≤ π n.succ ∧ π n.succ ≤ π n + 1 := by
  simp [π]
  constructor
  · apply card_le_of_subset
    apply filter_subset_filter
    simp only [Finset.range_subset, le_add_iff_nonneg_right, zero_le']
  · nth_rw 1 [range_succ]
    rw [filter_insert]
    split_ifs
    · rw [card_insert_of_not_mem _]
      simp only [Finset.not_mem_range_self, not_false_iff, Finset.mem_filter, false_and_iff]
    · apply Nat.le_succ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- We now derive some list lemmata.
-- `list_stuff_0` and `list_stuff_1` didn't turn out to be
-- useful to us and my be skipped. We kept them in here as
-- they may be mathlib material.
/-- If `a :: la` is a prefix of `b :: lb`, then `a = b`-/
theorem list_stuff_0 (a b : ℕ) (la lb : List ℕ) (h : (a::la) <+: b::lb) : a = b := by
  simp [List.IsPrefix] at h ; exact h.1

/-- If `la` is a prefix of `lb`, and `k` is smaller then
the length of `k`, the the `k`th element of lists
`la` and `lb` coincide.
-/
theorem list_stuff_1 (k : Nat) (la lb : List ℕ) (hp : la <+: lb) (hl : k < la.length) :
    la.nthLe k (by assumption) =
      lb.nthLe k
        (by
          apply lt_of_lt_of_le hl
          rw [List.IsPrefix] at hp
          cases' hp with t teq
          rw [← teq]
          simp only [List.length_append, le_add_iff_nonneg_right, zero_le']) := by
  revert la lb
  induction' k with k ih
  intro la lb h H
  cases' la with a la'
  exfalso; simp at H ; exact H
  cases' lb with b lb'
  exfalso; simp at h ; exact h
  simp
  exact list_stuff_0 a b la' lb' h
  intro la lb h H
  cases' la with a la'
  exfalso; simp at H ; exact H
  cases' lb with b lb'
  exfalso; simp at h ; exact h
  simp
  apply ih
  simp [List.IsPrefix] at *
  exact h.2

/-- If a list `l` is sorted, then for an index `k` such that
`k+1` is less then the lists length, the `k`th element of
list `l` will be `≤`  then the `k+1`th
-/
theorem list_stuff_2 (l : List Nat) (hl : List.Sorted (· ≤ ·) l) (k : Nat)
    (hk : k.succ < l.length) :
    l.nthLe k (by rw [Nat.succ_eq_add_one] at hk ; linarith) ≤ l.nthLe k.succ hk := by
  revert k
  induction' l with a l ih
  · intro k hk; exfalso; simp at hk ; exact hk
  intro k hk
  rw [List.sorted_cons] at hl
  cases k
  simp; apply hl.1; apply List.nthLe_mem
  simp; apply ih; exact hl.2

/-- If a list `l` has no duplicates, then for an index `k`
such that `k+1` is less then the lists length, the `k`th
element of list `l` will be different from the `k+1`th
-/
theorem list_stuff_3 (l : List Nat) (hl : List.Nodup l) (k : Nat) (hk : k.succ < l.length) :
    l.nthLe k (by rw [Nat.succ_eq_add_one] at hk ; linarith) ≠ l.nthLe k.succ hk := by
  revert k
  induction' l with a l ih
  · intro k hk; simp at hk ; exact False.elim hk
  intro k hk
  rw [List.nodup_cons] at hl
  cases k
  simp; intro con; rw [Con] at hl ; apply hl.1; apply List.nthLe_mem
  simp; apply ih; exact hl.2

/-- The `kth_prime_among` function increases by at leat 1 for successive indices.  -/
theorem kthPrimeAmong_increase (n k : ℕ) (h : k.succ < π n) :
    kthPrimeAmong n k (by rw [Nat.succ_eq_add_one] at h ; linarith) + 1 ≤
      kthPrimeAmong n k.succ h := by
  simp [kthPrimeAmong]
  rw [Nat.add_one_le_iff]
  apply lt_of_le_of_ne
  · apply list_stuff_2
    exact Finset.sort_sorted (· ≤ ·) (Filter Nat.Prime (range (n + 1)))
  · apply list_stuff_3
    exact Finset.sort_nodup (· ≤ ·) (Filter Nat.Prime (range (n + 1)))

/-- The lower bound on the `k`th prime: `k+2 ≤ kth_prime_among n k` -/
theorem kthPrimeAmong_bound (n k : ℕ) (h : k < π n) : k + 2 ≤ kthPrimeAmong n k h := by
  induction' k with k ih
  · rw [zero_add]
    apply Nat.Prime.two_le
    exact (kthPrimeAmong_makes_sense' n 0 h).2
  · have : _ := kthPrimeAmong_increase n k h
    apply le_trans _ this
    simp_rw [Nat.succ_eq_add_one k]
    linarith [ih
        (show k < π n by
          rw [Nat.succ_eq_add_one] at h
          apply lt_trans _ h
          exact lt_add_one k)]

/-- We bound the ordered product of primes using the bound `kth_prime_among_bound`-/
theorem prod_ordered_primes_bound_pre (n : ℕ) :
    ∏ k in (univ : Finset (Fin (π n))),
        (kthPrimeAmong n k.val k.Prop / (kthPrimeAmong n k.val k.Prop - 1) : ℚ) ≤
      ∏ k in (univ : Finset (Fin (π n))), ((k.val + 2) / (k.val + 1) : ℚ) := by
  have useful_tec : ∀ k : Fin (π n), Nat.Prime (kthPrimeAmong n k.val k.Prop) := by
    intro k
    exact (kthPrimeAmong_makes_sense' n k.val k.prop).2
  apply prod_le_prod
  · intro k kdef
    apply div_nonneg
    exact @Nat.cast_nonneg ℚ _ (kthPrimeAmong n k.val k.prop)
    rw [le_sub_iff_add_le]; rw [zero_add]; simp only [Nat.one_le_cast, Fin.val_eq_coe]
    exact le_of_lt (Nat.Prime.one_lt (useful_tec k))
  -- `nat.prime.one_le` doesn't exist
  · intro i idef
    -- We bring both sides in form (1 + 1/(1 ± x)) to makes comparison easier
    have :
      (kthPrimeAmong n i.val i.prop / (kthPrimeAmong n i.val i.prop - 1) : ℚ) =
        1 + (1 / (kthPrimeAmong n i.val i.prop - 1) : ℚ) := by
      have := sub_add_cancel (kthPrimeAmong n i.val i.prop : ℚ) (1 : ℚ)
      nth_rw 1 [← this]; clear this
      rw [add_div]
      simp only [one_div, Fin.val_eq_coe, add_left_inj]
      apply div_self
      intro con
      rw [sub_eq_iff_eq_add] at con
      rw [zero_add] at con
      apply Nat.Prime.ne_one (useful_tec i)
      rw [← @Nat.cast_inj ℚ _ _ _ _]
      apply Con
    rw [this]; clear this
    have : ((i.val + 2) / (i.val + 1) : ℚ) = 1 + 1 / (i.val + 1 : ℚ) := by
      rw [show (2 : ℚ) = 1 + 1 by norm_num]
      rw [← add_assoc]
      rw [add_div]
      simp only [one_div, Fin.val_eq_coe, add_left_inj]
      apply div_self
      exact Nat.cast_add_one_ne_zero i.val
    rw [this]; clear this
    simp only [one_div, Fin.val_eq_coe, add_le_add_iff_left]
    rw [inv_le_inv]
    -- We may now make use of `kth_prime_among_bound`
    · rw [le_sub_iff_add_le]; rw [add_assoc]; rw [← show (2 : ℚ) = 1 + 1 by norm_num]
      have coe_pull : ((i : ℕ) + 2 : ℚ) = ↑(i.val + 2) := by
        simp only [algebraMap.coe_one, Fin.val_eq_coe, add_left_inj, Nat.cast_bit0,
          eq_self_iff_true, Nat.cast_inj, Nat.cast_add]
      rw [coe_pull]
      rw [Nat.cast_le]
      apply kthPrimeAmong_bound n i.val i.prop
    · rw [lt_sub_iff_add_lt]
      rw [zero_add]
      simp only [Nat.one_lt_cast]
      exact Nat.Prime.one_lt (useful_tec i)
    · rw [← Nat.cast_add_one]
      have coe_pull : ↑0 = (0 : ℚ) := by simp only [algebraMap.coe_zero, eq_self_iff_true]
      rw [← coe_pull]
      rw [Nat.cast_lt]
      apply Nat.succ_pos

/-
A technical lemma about the fin-ℕ relation in products.
This is close to `fin.prod_univ_eq_prod_range`,
but seems to behave differently, as can be seen in
`prod_ordered_primes_bound`.
-/
theorem prod_fin_range (f : ℕ → ℚ) (n : ℕ) :
    ∏ k in (univ : Finset (Fin n)), f k.val = ∏ k in range n, f k := by
  --library_search, --fails
  apply prod_bij fun a : Fin n => fun auniv : a ∈ (univ : Finset (Fin n)) => a.val
  -- map
  intro a ha;
  simp only [Fin.is_lt, Fin.val_eq_coe, Finset.mem_range]
  -- equality
  intro a ha;
  simp only [Fin.val_eq_coe, eq_self_iff_true]
  -- injectivity
  intro a b ha hb;
  dsimp; rw [← Fin.val_eq_coe, ← Fin.val_eq_coe]; exact (Fin.eq_iff_veq a b).mpr
  --surjectivity
  intro b bdef;
  rw [mem_range] at bdef
  use⟨b, bdef⟩
  have ha : (⟨b, bdef⟩ : Fin n) ∈ univ := by refine' mem_univ ⟨b, bdef⟩
  use ha

-- #check fin.prod_univ_eq_prod_range
-- I didn't know about this one, before writing the proof
-- to the previous result, as you can guess from the failed
-- library search.
-- #check prod_range_div
-- Requires a commutative group, which (ℚ,×) isn't
/-- A technical lemma for telescoping, without having to
cast to ℚ* so as to be able to use `prod_range_div`
-/
theorem prod_range_telescope (f : ℕ → ℚ) (n : ℕ) (h : ∀ n : ℕ, f n ≠ 0) :
    ∏ k in range n, f k.succ / f k = f n / f 0 := by
  --library_search, --fails
  apply prod_range_induction
  · apply div_self
    exact h 0
  · intro n
    rw [mul_comm]
    rw [div_mul_div_cancel]
    exact h n

/-- Upper-bounds the ordered product of primes by the prime counting function-/
theorem prod_ordered_primes_bound (n : ℕ) :
    ∏ k in (univ : Finset (Fin (π n))),
        (kthPrimeAmong n k.val k.Prop / (kthPrimeAmong n k.val k.Prop - 1) : ℚ) ≤
      π n + 1 := by
  apply le_of_le_of_eq (prod_ordered_primes_bound_pre n)
  rw [prod_fin_range (fun k => ((k + 2) / (k + 1) : ℚ)) (π n)]
  -- simp_rw fin.val_eq_coe,
  --rw fin.prod_univ_eq_prod_range (λ k, ((k+2)/(k+1) : ℚ)) (π n),
  --alternative to the previous line
  dsimp
  simp_rw [show (2 : ℚ) = 1 + 1 by norm_num, ← add_assoc]
  --rw prod_range_div (λ x, (x + 1 : ℚ)) (π n),
  -- telescoping with this would require working in ℚ*
  -- as a multiplicative group, which requires casting
  simp_rw [show ∀ x : ℕ, (x : ℚ) + 1 = (x.succ : ℚ) by norm_num]
  rw [prod_range_telescope fun x => (x.succ : ℚ)]
  · simp
  · intro m
    dsimp
    intro con
    have : (0 : ℚ) = ((0 : ℕ) : ℚ) := by simp
    rw [this] at con
    rw [Nat.cast_inj] at con
    exact (Nat.succ_ne_zero m) Con

-- #check prod_attach
--This serves as a good example for library search inflexibility
theorem prod_set_attach {α : Type} [CommMonoid α] (f : ℕ → α) (s : Finset ℕ) :
    ∏ k in s.attach, f k.val = ∏ k in s, f k := by
  --library_search, --fails
  apply prod_bij fun x : { x // x ∈ s } => fun h : x ∈ s.attach => x.val
  simp
  simp
  simp
  simp

/-- Rewrites the product of primes in a form suitable
to introduce sums of geometric series.
-/
theorem rw_the_prod {n : ℕ} :
    ∏ p in (range (n + 1)).filter fun p => Nat.Prime p, (p / (p - 1) : ℚ) =
      ∏ p in (range (n + 1)).filter fun p => Nat.Prime p, (1 / (1 - 1 / p) : ℚ) := by
  rw [← prod_attach]
  nth_rw 2 [← prod_attach]
  congr; apply funext; rintro p
  have : (1 : ℚ) - 1 / ↑↑p = (↑↑p - 1) / ↑↑p := by
    rw [sub_div]; rw [div_self]
    intro con
    have : (0 : ℚ) = ((0 : ℕ) : ℚ) := by simp
    rw [this] at con ; clear this
    rw [Nat.cast_inj] at con
    have := p.prop; rw [mem_filter] at this
    exact (Nat.Prime.ne_zero this.2) Con
  rw [this]
  simp only [eq_self_iff_true, one_div_div]

-- This lemma isn't actually used
theorem geom_sum_Icc_le_one_div_of_lt_one {α : Type} [_inst_1 : LinearOrderedField α] {x : α} :
    0 ≤ x → x < 1 → ∀ {n : ℕ}, ∑ i : ℕ in Icc 1 n, x ^ i ≤ 1 / (1 - x) := by
  intro xpos xleone n
  have : Icc 1 n = Ico 1 (n + 1) := by
    --library_search, -- → todo
    ext x;
    constructor
    intro icc; rw [mem_Icc] at icc ; rw [mem_Ico]; constructor; linarith; linarith
    intro ico; rw [mem_Ico] at ico ; rw [mem_Icc]; constructor; linarith; linarith
  rw [this]
  apply le_trans (geom_sum_Ico_le_of_lt_one xpos xleone)
  apply div_le_div
  exact zero_le_one
  rw [pow_one]; exact le_of_lt xleone
  linarith
  apply le_refl

/-- An isolated step of for `prod_sum_bound` -/
theorem prod_sum_bound_pre {n p : ℕ} (hp : p ∈ (range (n + 1)).filter fun p => Nat.Prime p) :
    ∑ k in Ico 0 (n + 1), ((1 / p) ^ k : ℚ) ≤ 1 / (1 - 1 / p) := by
  nth_rw 1 [← pow_zero (1 / p : ℚ)]
  apply geom_sum_Ico_le_of_lt_one
  · apply div_nonneg
    exact zero_le_one
    rw [show (0 : ℚ) = ((0 : ℕ) : ℚ) by simp]
    rw [Nat.cast_le]
    exact zero_le p
  · rw [mem_filter] at hp
    -- If we don't rw here, we'll have to rw multiple times,
    -- once for each subgoal
    rw [div_lt_iff]
    rw [one_mul]
    rw [show (1 : ℚ) = ((1 : ℕ) : ℚ) by simp]
    rw [Nat.cast_lt]
    exact Nat.Prime.one_lt hp.2
    rw [show (0 : ℚ) = ((0 : ℕ) : ℚ) by simp]
    rw [Nat.cast_lt]
    exact Nat.Prime.pos hp.2

/-
Upper-bounds the product of geometric sums by
the product of primes.
-/
theorem prod_sum_bound {n : ℕ} :
    ∏ p in (range (n + 1)).filter fun p => Nat.Prime p, ∑ k in Ico 0 (n + 1), ((1 / p) ^ k : ℚ) ≤
      ∏ p in (range (n + 1)).filter fun p => Nat.Prime p, (p / (p - 1) : ℚ) := by
  rw [rw_the_prod]
  apply prod_le_prod
  · intro i idef
    apply sum_nonneg
    intro j jdef
    apply pow_nonneg
    apply div_nonneg
    exact zero_le_one
    apply Nat.cast_nonneg
  · intro p pdef
    exact prod_sum_bound_pre pdef

/-- First step in linking the hamronic series to the
produc of geometric sums:
distributing the product of sums.
-/
theorem the_great_split_part_1 {n : ℕ} :
    ∏ p in (range (n + 1)).filter fun p => Nat.Prime p, ∑ k in Ico 0 (n + 1), ((1 / p) ^ k : ℚ) =
      ∑ valu in ((range (n + 1)).filter fun p => Nat.Prime p).pi fun p => Ico 0 (n + 1),
        ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach,
          ((1 / p.val) ^ valu p.val p.Prop : ℚ) :=
  by apply prod_sum

/-- Second step in linking the hamronic series to the
produc of geometric sums:
lower-bounding the distributing the product of sums
by the sum on the subset obtained by filtering out
the terms who's value isn a 1/k for k∈[n].
-/
theorem the_great_split_part_2 {n : ℕ} :
    ∑ valu in
        filter
          (fun valu : ∀ a : ℕ, a ∈ filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) → ℕ =>
            ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach,
                p.val ^ valu p.val p.Prop ∈
              Icc 1 n)
          (((range (n + 1)).filter fun p => Nat.Prime p).pi fun hmm => Ico 0 (n + 1)),
        (1 /
            ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach,
              p.val ^ valu p.val p.Prop :
          ℚ) ≤
      ∑ valu in ((range (n + 1)).filter fun p => Nat.Prime p).pi fun hmm => Ico 0 (n + 1),
        (1 /
            ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach,
              p.val ^ valu p.val p.Prop :
          ℚ) := by
  apply sum_le_sum_of_subset_of_nonneg
  · apply filter_subset
  · intro i it ins
    rw [one_div]
    rw [inv_nonneg]
    apply prod_nonneg
    intro j jdef
    apply pow_nonneg
    apply Nat.cast_nonneg

/-- A lemma that should be in mathlib, in my opinion.
Used in `quick_prime_decompo`.
-/
theorem prod_one {α : Type} [DecidableEq α] (s : Finset α) : ∏ i in s, 1 = 1 := by
  --library_search, --fails
  apply Finset.induction_on s
  rw [prod_empty]
  intro a s ans ih
  rw [prod_insert]
  rw [ih]
  exact one_mul 1
  exact ans

-- apply prod_eq_one,
-- intros x xs,
-- refl,
-- alternative proof to the previous one
-- In my defense: why is it not "prod_one" ?
/-
For `the_great_split_part_3`, we need to show that all
numbers have a prime decomposition.
There are multiple notions of factorisation in mathlib,
which we now present
-/
-- This one I came accross only in the clean up phase of this file
-- #check nat.factorization
#eval Nat.factorization 2023 7

--the valuation of prime factor 7 in 2023
-- Prime decomposition present as `factorization_prod_pow_eq_self`,
-- in terms of finsupp, not in the form:
-- example (n : ℕ):
--   n = ∏ f in n.factors.to_finset, f^(n.factorization f) :=
--     by {--library_search, --fails
--         }
-- This one I new about before formalizing `quick_prime_decompo`,
-- but it didn't appear useful, as it had no valuations ...
-- #check nat.factors
#eval Nat.factors 9

-- ... and prime decomposition was in the form of a product
-- over a list, where valuations made no appearance.
-- #check nat.prod_factors
-- #check nat.factorization_prod_pow_eq_self
/-- Prime decomposition in the form of a function, in the sense that:
For each number `m` in 1,...,n, there is a valuation function `valu`
that has as inputs the primes in 1,...,n (as a pi-type), and returns
the power of that prime in the prime decomposition of `m`.
-/
theorem quick_prime_decompo {n : ℕ} (m : ℕ) (mdef : m ∈ Icc 1 n) :
    ∃ valu : ∀ valu : ℕ, valu ∈ filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) → ℕ,
      m =
        ∏ x : { x // x ∈ filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) } in
          (filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach, ↑x ^ valu (↑x) x.Prop := by
  revert mdef
  -- We use strong induciton on `m`
  apply Nat.strong_induction_on m
  intro M ih Mdef
  -- We disjoin cases on whether M is prime, in which case the
  -- valuation is the indicator of M, ...
  by_cases Mprime : Nat.Prime M
  · set valuM := fun (p : ℕ) (pdef : p ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))) =>
      if p = M then 1 else 0 with valuMdef
    use valuM
    rw [valuMdef]
    simp_rw [pow_ite]
    rw [prod_ite]
    simp_rw [pow_zero]
    rw [Finset.prod_const_one]
    rw [mul_one]
    simp_rw [pow_one]
    have simpli_the_set :
      Filter (fun x : { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) } => ↑x = M)
          (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach =
        {(⟨M, by rw [mem_filter]; constructor; rw [mem_range]; rw [mem_Icc] at Mdef ; linarith;
              exact Mprime⟩ :
            { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) })} := by
      ext x
      constructor
      · intro xfil
        simp only [true_and_iff, Finset.mem_attach, Finset.mem_filter] at xfil
        rw [mem_singleton]
        apply Subtype.eq
        apply xfil
      · intro xsingle
        simp only [true_and_iff, Finset.mem_attach, Finset.mem_filter]
        rw [mem_singleton] at xsingle
        --finish, -- works but slows down compilation
        rw [xsingle]
        dsimp
        rfl
    rw [simpli_the_set]
    rw [prod_singleton]
    dsimp; rfl
  -- ... or M is not prime, in which case we factor it,
  -- and apply the induction hypothesis.
  -- We need to consider the case of M = 1 as well.
  apply ltByCases M 1
  -- A technical and impossible case
  · intro c_lt_one
    rw [Nat.lt_one_iff] at c_lt_one
    rw [c_lt_one] at Mdef
    exfalso
    rw [mem_Icc] at Mdef
    norm_num at Mdef
  -- Case of M = 1: use the 0 valuation
  · intro c_eq_one
    use fun p pdef => 0
    simp_rw [pow_zero]
    rw [prod_one (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach]
    exact c_eq_one
  -- We may finally factor and use the induction assumption
  · intro two_le_M
    obtain ⟨P, ⟨P_def, facto⟩⟩ := Nat.exists_prime_and_dvd (ne_of_gt two_le_M)
    -- In order to apply ih to P, we need the follwoing facts
    have PltM : P < M := by
      rw [mem_Icc] at Mdef
      apply lt_of_le_of_ne
      · apply Nat.le_of_dvd _ facto
        exact lt_of_lt_of_le zero_lt_one Mdef.1
      · intro con
        rw [Con] at P_def
        exact Mprime P_def
    have P_Icc : P ∈ Icc 1 n := by
      rw [mem_Icc] at *
      constructor
      · exact le_of_lt (Nat.Prime.one_lt P_def)
      · apply le_trans _ Mdef.2
        exact le_of_lt PltM
    cases' facto with d facto
    -- Same thing with the other factor
    have dltM : d < M := by
      rw [mem_Icc] at Mdef
      apply lt_of_le_of_ne
      · have d_dvd := dvd_of_mul_left_eq P facto.symm
        apply Nat.le_of_dvd _ d_dvd
        exact lt_of_lt_of_le zero_lt_one Mdef.1
      · intro con
        rw [Con] at facto
        rw [eq_comm] at facto
        rw [Nat.mul_left_eq_self_iff _] at facto
        exact (Nat.Prime.ne_one P_def) facto
        exact lt_trans zero_lt_one two_le_M
    have d_Icc : d ∈ Icc 1 n := by
      rw [mem_Icc] at *
      constructor
      · by_contra! con
        rw [Nat.lt_one_iff] at con
        rw [Con] at facto
        rw [MulZeroClass.mul_zero] at facto
        rw [facto] at two_le_M
        -- exact not_one_lt_zero, -- mathlib ?
        linarith
      · exact le_trans (le_of_lt dltM) Mdef.2
    -- We apply the induction hypothesis
    obtain ⟨P_valu, P_valu_def⟩ : _ := ih P PltM P_Icc
    obtain ⟨d_valu, d_valu_def⟩ : _ := ih d dltM d_Icc
    -- The valuation of a product is the sum of valuations
    use fun p pdef => P_valu p pdef + d_valu p pdef
    rw [facto]
    rw [d_valu_def, P_valu_def]
    rw [← prod_mul_distrib]
    simp_rw [← pow_add]

/-- A fibering lemma:
For a surjective map `i` as Pi-Types, so as to constrain it
to have domain `s`, with values in `t`,
- The preimages under `f` of the elements of `t` form a disjoint family
- `s` is a union of these perimages
-/
theorem surj_partition {α γ : Type} [DecidableEq α] [DecidableEq γ] {s : Finset α} {t : Finset γ}
    (i : ∀ a ∈ s, γ) (imap : ∀ a ha, i a ha ∈ t) (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) :
    ((t : Set γ).PairwiseDisjoint fun x => s.attach.filter fun y => x = i y.val y.Prop) ∧
      s.attach = t.biUnion fun x => s.attach.filter fun y : { z // z ∈ s } => x = i y.val y.Prop := by
  constructor
  · intro a ait b bit anb
    dsimp
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp only [true_and_iff, Finset.not_mem_empty, Finset.mem_attach, not_and, Finset.mem_filter,
      iff_false_iff, Finset.mem_inter]
    intro eqa eqb
    apply anb
    rw [eqa, eqb]
  · ext x
    constructor
    · intro xs
      rw [mem_bUnion]
      use i x.val x.prop
      constructor
      exact imap x.val x.prop
      rw [mem_filter]
      constructor
      exact xs
      rfl
    intro xuni
    apply mem_attach s x

/-
It may very well be possible that the previous lemma is present in mathlib.
However, with libreary_serach failing, an nomenclature showing its limitations,
I proved it instead of looking further.
-/
-- #check bUnion_filter_eq_of_maps_to -- could you have guessed the name ?
-- #check pairwise_disjoint_of_maps_to --fails
/-
The following come close to what we want, and may possibly be used
as alternative in `sum_nonneg_surj`. However, the entire formalization
would have to be changed, as they don't work with Pi-types
-/
-- #check disj_Union_filter_eq_of_maps_to
-- #check sum_disj_Union
/-- For a nonnegative function `f` on `s`, and some `x∈s`, `f x ≤ ∑ y in s, f y`.
-/
theorem le_sum_mem_nonneg {α β : Type} [DecidableEq α] [OrderedAddCommMonoid β] {s : Finset α}
    (f : α → β) (hf : ∀ a, a ∈ s → 0 ≤ f a) (x : α) (hx : x ∈ s) : f x ≤ ∑ y in s, f y := by
  rw [← insert_erase hx]
  rw [sum_insert]
  swap
  · apply not_mem_erase
  · nth_rw 1 [← add_zero (f x)]
    apply add_le_add_left
    apply sum_nonneg
    intro i idef
    exact hf i ((erase_subset x s) idef)

/-- If we have a surjection `i` from `s` to `t` (as a Pi-type), and
functions `f` and `g` such that `f` is nonnegative and ` ∀ a ha, f a = g (i a ha)`,
then we may bound `(∑ x in t, g x) ≤ (∑ x in s, f x)`.
-/
theorem sum_nonneg_surj {α β γ : Type} [DecidableEq α] [DecidableEq γ] [OrderedAddCommMonoid β]
    {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t)
    (h : ∀ a ha, f a = g (i a ha)) (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha)
    (nonneg_fun : ∀ a, a ∈ s → 0 ≤ f a) : ∑ x in t, g x ≤ ∑ x in s, f x := by
  rw [← sum_attach]; rw [← @sum_attach _ _ s _ f]
  obtain ⟨disj_fact, eq_fact⟩ : _ := surj_partition i hi i_surj
  rw [eq_fact]
  rw [sum_bUnion disj_fact]
  rw [← @sum_attach _ _ t _ _]
  apply sum_le_sum
  intro j jdef; simp
  obtain ⟨k, ⟨kdef, keq⟩⟩ := i_surj j.val j.prop
  rw [← Subtype.val_eq_coe]
  rw [keq]
  rw [← h k kdef]
  have unsimp : f k = f (⟨k, kdef⟩ : { x // x ∈ s }) := by
    simp only [eq_self_iff_true, Subtype.coe_mk]
  rw [unsimp]; clear unsimp
  apply le_sum_mem_nonneg fun x : { x // x ∈ s } => f ↑x
  swap
  · rw [mem_filter]
    constructor
    apply mem_attach
    simp only [eq_self_iff_true, Subtype.coe_mk]
  · intro a adef
    simp only
    exact nonneg_fun (↑a) a.prop

-- An alias ?
theorem Nat.pos_iff_one_le {n : ℕ} : 0 < n ↔ 1 ≤ n :=
  Nat.lt_iff_add_one_le

-- A technical lemma used in `the_great_split_part_3`.
--For standard versions, consider the the #check that follow.
theorem Nat.le_prod_mem_pos {α : Type} [DecidableEq α] {s : Finset α} (f : α → ℕ)
    (hf : ∀ a, a ∈ s → 0 < f a) (x : α) (hx : x ∈ s) : f x ≤ ∏ y in s, f y := by
  rw [← insert_erase hx]
  rw [prod_insert]
  swap
  apply not_mem_erase
  nth_rw 1 [← mul_one (f x)]
  apply Nat.mul_le_mul_left
  rw [← zero_add 1]
  rw [← Nat.lt_iff_add_one_le]
  apply prod_pos
  intro i idef; apply hf i _
  exact (erase_subset x s) idef

-- These have slightly different conditions and conclusions
-- Also, I didn't know the nomancalture for them
-- #check single_le_prod'
-- #check single_lt_prod'
-- An inequality used in `the_great_split_part_3`
theorem tec_ineq (n : ℕ) : n < 2 ^ (n + 1) := by
  induction' n with n ih
  norm_num
  rw [Nat.succ_eq_add_one]
  rw [pow_add, pow_one, mul_two]
  apply Nat.add_lt_add
  exact ih
  exact Nat.one_lt_pow' n 0

/-- Final step in linking the hamronic series to the
produc of geometric sums:
upper-bound the harmonic sum with the filtered
sum of products.
-/
theorem the_great_split_part_3 {n : ℕ} :
    ∑ k in Icc 1 n, (1 / k : ℚ) ≤
      ∑ valu in
        filter
          (fun valu : ∀ a : ℕ, a ∈ filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) → ℕ =>
            ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach,
                p.val ^ valu p.val p.Prop ∈
              Icc 1 n)
          (((range (n + 1)).filter fun p => Nat.Prime p).pi fun hmm => Ico 0 (n + 1)),
        (1 /
            ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach,
              p.val ^ valu p.val p.Prop :
          ℚ) := by
  -- i maps a valuation to the product of primes with these valuations
  set i :=
    fun (valu : ∀ a : ℕ, a ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) → ℕ)
      (valu_def :
        valu ∈
          Filter
            (fun valu : ∀ a : ℕ, a ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) → ℕ =>
              ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach,
                  p.val ^ valu p.val p.Prop ∈
                Icc 1 n)
            (((range (n + 1)).filter fun p => Nat.Prime p).pi fun hmm => Ico 0 (n + 1))) =>
    ∏ p in ((range (n + 1)).filter fun p => Nat.Prime p).attach, p.val ^ valu p.val p.Prop with
    idef
  apply sum_nonneg_surj i
  -- i maps one set of the sum to the other
  · intro valu valu_def
    rw [idef]
    simp only [Finset.mem_Icc, Finset.prod_congr, Subtype.val_eq_coe]
    constructor
    · apply one_le_prod''
      intro p
      apply Nat.one_le_pow
      apply Nat.Prime.pos
      have := p.prop
      rw [mem_filter] at this
      exact this.2
    · rw [mem_filter] at valu_def
      simp only [Finset.mem_Icc, Finset.mem_pi, Finset.prod_congr, Subtype.val_eq_coe] at valu_def
      exact valu_def.2.2
  -- equality of the images on the sets, when composing with i
  · intro valu valu_def
    rw [idef]
    simp only [Nat.cast_prod, one_div, eq_self_iff_true, inv_inj, Finset.prod_congr, Nat.cast_pow,
      Subtype.val_eq_coe]
  swap
  --nonnegativity of the functions we're comparing
  · intro valu valu_def
    simp only [one_div, inv_nonneg, Finset.prod_congr, Subtype.val_eq_coe]
    apply prod_nonneg
    intro j jdef
    apply pow_nonneg
    apply Nat.cast_nonneg
  -- surjectivity : this is where we need `quick_prime_decompo`
  · intro m mdef
    rw [idef]
    simp
    obtain ⟨valu, valu_def⟩ : _ := quick_prime_decompo m mdef
    use valu; constructor
    · constructor
      · -- We show that the valuation can't exceed n+1
        intro p pdef
        by_contra! con
        -- First, we show that a factor (with multiplicity) can't exceed the product
        have :
          ↑(⟨p, by rw [mem_filter]; rw [mem_range]; exact pdef⟩ :
                  { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) }) ^
              valu
                (↑(⟨p, by rw [mem_filter]; rw [mem_range]; exact pdef⟩ :
                    { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) }))
                (by rw [mem_filter]; rw [mem_range]; exact pdef) ≤
            m := by
          rw [valu_def]
          apply
            Nat.le_prod_mem_pos
              fun x : { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) } =>
              ↑x ^ valu (↑x) x.Prop
          · intro q qdef; simp; apply pow_pos; apply Nat.Prime.pos
            have : _ := q.prop; rw [mem_filter] at this ; exact this.2
          apply mem_attach
        simp only [Subtype.coe_mk] at this
        -- We lower bound the prime factor and make use of the
        -- contradictory assumption `con` to get the following:
        have problem : 2 ^ (n + 1) ≤ m := by
          calc
            2 ^ (n + 1) ≤ p ^ (n + 1) := by
              apply Nat.pow_le_pow_left
              apply Nat.Prime.two_le
              exact pdef.2
            _ ≤ p ^ valu p (by rw [mem_filter]; rw [mem_range]; exact pdef) := by
              apply Nat.pow_le_pow_right
              apply Nat.Prime.pos
              exact pdef.2
              exact Con
            _ ≤ m := this
        -- We use this bound and the assumption on `m` to
        -- contradict `2^(n+1)>n`
        rw [mem_Icc] at mdef
        apply lt_irrefl n
        apply lt_of_lt_of_le (tec_ineq n)
        apply le_trans problem mdef.2
      -- Some boudns that follow from `mdef` and `valu_def`
      · rw [← valu_def]
        rw [mem_Icc] at mdef
        exact mdef
    exact valu_def

/-- The center piece.
We lower-bound the prime counting function by the harminic series!
-/
theorem the_great_merger {n : ℕ} : ∑ k in Icc 1 n, (1 / k : ℚ) ≤ π n + 1 := by
  apply le_trans the_great_split_part_3
  apply le_trans the_great_split_part_2
  -- We have a rewrite of form 1/∏x = ∏1/x
  have rw_tec :
    ∀ valu : ∀ a : ℕ, a ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) → ℕ,
      (1 : ℚ) /
          ∏ p : { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) } in
            (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach,
            (p.val ^ valu p.val p.Prop : ℚ) =
        ∏ p : { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) } in
          (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach,
          (1 / p.val ^ valu p.val p.Prop : ℚ) := by
    intro valu
    nth_rw 1 [←
      @prod_eq_one _ _ _ (fun x => (1 : ℚ))
        (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach (by intro x xdef; rfl)]
    apply prod_div_distrib.symm
  simp_rw [rw_tec]
  -- We have a rewrite of form 1/(x^p) = (1/x)^p
  have rw_tec_2 :
    ∀ valu : ∀ a : ℕ, a ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) → ℕ,
      ∏ p : { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) } in
          (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach,
          (1 / p.val ^ valu p.val p.Prop : ℚ) =
        ∏ p : { x // x ∈ Filter (fun p : ℕ => Nat.Prime p) (range (n + 1)) } in
          (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).attach,
          ((1 / p.val) ^ valu p.val p.Prop : ℚ) :=
    by simp_rw [div_pow]; simp_rw [one_pow]; intro valu; rfl
  simp_rw [rw_tec_2]
  clear rw_tec_2 rw_tec
  -- We may now use:
  rw [← the_great_split_part_1]
  -- The great split is over, now we chain the bounds
  apply le_trans prod_sum_bound
  rw [order_the_prod]
  apply prod_ordered_primes_bound

-- Another technical lemma that's mathlib material
theorem Nat.Icc_split (a b c : ℕ) (h1 : b ≤ c) (h2 : a ≤ b + 1) :
    Disjoint (Icc a b) (Icc (b + 1) c) ∧ Icc a c = Icc a b ∪ Icc (b + 1) c := by
  constructor
  · rw [Disjoint]
    intro x xl xt
    simp only [Finset.bot_eq_empty, Finset.le_eq_subset]
    intro y yx
    -- rw @set.mem_empty_iff_false ℕ y, --hmm
    specialize xl yx
    specialize xt yx
    rw [mem_Icc] at *
    linarith
  · ext x
    constructor
    · intro xb
      rw [mem_union]
      rw [mem_Icc] at *
      by_cases q : x ≤ b
      left
      exact ⟨xb.1, q⟩
      push_neg at q
      rw [Nat.lt_iff_add_one_le] at q
      right
      rw [mem_Icc]
      exact ⟨q, xb.2⟩
    · intro xu
      rw [mem_union] at xu
      rw [mem_Icc] at *
      cases xu
      exact ⟨xu.1, le_trans xu.2 h1⟩
      rw [mem_Icc] at *
      exact ⟨le_trans h2 xu.1, xu.2⟩

/-- Lower-bounding harminoc sums up to the `2^n`th term by `n/2`.
-/
theorem harmonic_lb : ∀ n : ℕ, (n / 2 : ℚ) ≤ ∑ k in Icc 1 ((2 : ℕ) ^ n), (1 / k : ℚ) := by
  intro n
  induction' n with n ih
  ·
    simp only [one_div, algebraMap.coe_zero, zero_le_one, algebraMap.coe_one, Nat.zero_eq, zero_div,
      Finset.Icc_self, inv_one, Finset.sum_singleton, pow_zero, Finset.sum_congr]
  · rw [Nat.succ_eq_add_one]
    -- We split the sum in half by splitiing the interval in half
    obtain ⟨split_disj, split_union⟩ :=
      Nat.Icc_split 1 (2 ^ n) (2 ^ (n + 1)) (by apply pow_le_pow_right; norm_num; apply Nat.le_succ)
        le_add_self
    rw [split_union]
    rw [sum_union split_disj]
    push_cast
    rw [add_div]
    -- We may use the induciton hypothesis to handle the first half
    apply add_le_add ih
    clear split_disj split_union
    -- Next we work on lower-bounding the other half by the sum
    -- of its smallest term
    have rw_half : (1 / 2 : ℚ) = (2 ^ n / 2 ^ (n + 1) : ℚ) := by
      rw [div_eq_div_iff]
      · rw [one_mul]
        nth_rw_rhs 2 [← @pow_one ℚ _ 2]
        rw [← pow_add]
      · norm_num
      · apply ne_of_gt
        apply pow_pos
        norm_num
    rw [rw_half]; clear rw_half
    rw [div_eq_mul_one_div]
    -- This will be the size of the constant sum:
    have Icc_size : (Icc (2 ^ n + 1) (2 ^ (n + 1))).card = 2 ^ n := by
      rw [Nat.card_Icc]
      rw [Nat.sub_eq_iff_eq_add _]
      · rw [← add_assoc]
        rw [← mul_two]
        rw [Nat.succ_inj']
        rw [pow_add, pow_one]
      · apply Nat.succ_le_succ
        apply pow_le_pow_right
        norm_num
        apply Nat.le_succ
    apply_fun fun x => (x : ℚ) at Icc_size
    push_cast at Icc_size
    rw [show (0 : ℚ) + 1 + 1 = 2 by norm_num] at Icc_size
    rw [← Icc_size]; clear Icc_size
    -- Here, we introduce the constant sum:
    rw [card_eq_sum_ones]
    push_cast
    rw [sum_mul]
    -- We may now proceed with bounding terms:
    rw [show (0 : ℚ) + 1 = 1 by norm_num]
    apply sum_le_sum
    intro k kdef
    rw [one_mul]
    rw [one_div, one_div]
    rw [inv_le_inv]
    · rw [show (2 ^ (n + 1) : ℚ) = ↑(2 ^ (n + 1)) by simp]
      rw [Nat.cast_le]
      rw [mem_Icc] at kdef
      exact kdef.2
    · apply pow_pos
      norm_num
    · rw [Nat.cast_pos]
      rw [mem_Icc] at kdef
      apply lt_of_lt_of_le _ kdef.1
      apply Nat.succ_pos

/-- The harmonic series in unbounded-/
theorem harmonic_unbounded : ¬∃ b : ℕ, ∀ n : ℕ, ∑ k in Icc 1 n, (1 / k : ℚ) < b := by
  push_neg
  intro b
  use 2 ^ (2 * b)
  apply le_of_eq_of_le _ (harmonic_lb (2 * b))
  simp only [algebraMap.coe_one, Nat.cast_bit0, Nat.cast_mul]
  -- rw mul_div_cancel''' --(ℚ, ×) is no a group
  rw [mul_div_cancel_left]
  norm_num

/-- ### 4th proof of the infinitude of primes

We introduce the prime counting function `π`, which we
lower-bound by a certain product on prime numbers.

This product can be lower-bounded further until we reach
an expression that corresponds to a factored version of
the harmonic sums.

Thus, we bounded the prime counting function by the
harmonic series, which is unbounded, so that there must
be infinitely many primes.
-/
theorem fourth_proof : {n : ℕ | n.Prime}.Infinite := by
  rw [Set.Infinite]
  intro con
  -- We consider the number of primes
  set a := con.to_finset.card with adef
  -- Next, we get a larger harmonic sum
  have bound_pre := harmonic_unbounded
  push_neg at bound_pre
  obtain ⟨n, bound⟩ := bound_pre (a + 2)
  clear bound_pre
  -- then we use our bound
  replace bound := le_trans bound the_great_merger
  rw [π] at bound
  -- However, the card is of a set contained in the set of all primes
  have problem : (Filter (fun p : ℕ => Nat.Prime p) (range (n + 1))).card ≤ a := by
    rw [adef]
    apply card_le_of_subset
    intro x xdef
    rw [mem_filter] at xdef
    rw [Set.Finite.mem_toFinset Con]
    rw [Set.mem_setOf_eq]
    exact xdef.2
  simp only [algebraMap.coe_one, Nat.cast_bit0, Nat.cast_add] at bound
  apply_fun fun x : ℕ => (x : ℚ) at problem
  -- The bounds lead to a contradiciton
  linarith

-- #check fourth_proof
