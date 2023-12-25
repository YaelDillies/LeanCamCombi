/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Basic

/-!
# Six proofs of the inﬁnity of primes : 5th proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize the "Fifth proof",
which makes use of Topology.


## Structure

- `fifth_proof` :
      We show that there are infinitely many primes,
      in the standardised sense for infinity.
- `bona_fide_topology` :
      Is the topology on ℤ we use throughout the proof.
      It's based on the sets `N`.
- `two_units_not_open` :
      Is the proof that the pathological set {-1,1} isn't open.
- `univ_sdiff_units_as_prime_union` :
      Is the proof that {-1,1}ᶜ is a union of closed sets,
      indexed by the primes.


-/


--Deleting this import will yield unexpected errors
--Deleting this import will yield unexpected errors
/-- Two-way infinite arithmetic progressions-/
def n (a b : ℤ) : Set ℤ :=
  {x | ∃ n : ℤ, x = a + b * n}

/-- The curious topology on ℤ -/
instance bonaFideTopology : TopologicalSpace ℤ
    where
  -- First, we define the property of a set being open in the topology
  IsOpen O := O = ∅ ∨ ∀ a ∈ O, ∃ b : ℤ, 0 < b ∧ n a b ⊆ O
  -- The universal set should be open
  isOpen_univ := by
    --simp, use 1, exact zero_lt_one, -- the power of simp
    right
    intro a _
    use 1
    use zero_lt_one
    apply Set.subset_univ
  -- Intersections of open sets should be open
  isOpen_inter := by
    intro s t sO tO
    -- First, we discuss the empty cases
    obtain rfl | sO := sO;
    left; exact Set.empty_inter t
    obtain rfl | tO := tO
    · left; exact Set.inter_empty s
    -- Next come the non-empty cases
    right
    intro a auniv
    specialize sO a; specialize tO a
    have ais : a ∈ s := Set.mem_of_mem_inter_left auniv
    have ait : a ∈ t := Set.mem_of_mem_inter_right auniv
    specialize sO ais; specialize tO ait; clear ais ait
    rcases sO with ⟨bs, ⟨bs_tec, sIn⟩⟩; rcases tO with ⟨bt, ⟨bt_tec, tIn⟩⟩
    -- The common terms of the progressions is the progression with lcm bs bt
    -- as step, but that with step bs*bt (which is contained in the first),
    -- does the job too.
    refine ⟨bs * bt, mul_pos bs_tec bt_tec, ?_⟩
    simp only [n, Set.subset_inter_iff]
    constructor
    intro x xdef
    cases' xdef with xn xeq
    have : x ∈ n a bs := by rw [n]; use bt * xn; rw [← mul_assoc]; exact xeq
    exact sIn this
    intro x xdef; cases' xdef with xn xeq
    have : x ∈ n a bt := by rw [n]; use bs * xn; rw [← mul_assoc]; simpa only [mul_comm] using xeq
    exact tIn this
  -- Arbitrary unions of open sets should be open
  isOpen_sUnion := by
    intro fam fam_isO
    right
    intro a aunion
    rw [Set.mem_sUnion] at aunion ; rcases aunion with ⟨s, ⟨sfam, as⟩⟩
    specialize fam_isO s sfam
    obtain fam_isO | fam_isO := fam_isO
    exfalso; rw [fam_isO] at as ; exact Set.not_mem_empty a as
    specialize fam_isO a as
    rcases fam_isO with ⟨b, ⟨b_tec, incl⟩⟩
    use b; use b_tec
    refine' Set.Subset.trans incl _
    -- apply leads to a strange error
    exact Set.subset_sUnion_of_mem sfam

/-- Expressing the complement of a two-way arithmetic progression
as a finite union of two-way arithmetic progressions.

This allows us to show that N is closed, in the next lemma.
-/
theorem n_as_a_complement (a b : ℤ) (b_tec : 0 < b) :
    (n a b)ᶜ = ⋃ i ∈ Finset.Ico 1 b, n (a + i) b := by
  ext x
  simp
  -- the suggested "simp only" is not enough to get the same result.
  constructor
  · intro xcomp
    -- If x isn't on the arithmetic progression, we can consider
    -- its "remainder" modulo the progression
    use(x - a) % b
    constructor; constructor
    · by_contra! con
      have problem : (x - a) % b = 0 := by linarith [Int.emod_nonneg (x - a) (ne_of_gt b_tec)]
      clear con
      rw [← Int.dvd_iff_emod_eq_zero] at problem
      cases' problem with d ddef
      apply xcomp
      simp only [n, Set.mem_setOf_eq]
      use d
      rw [sub_eq_iff_eq_add] at ddef
      rwa [add_comm] at ddef
    -- Note the use of rwa
    · exact Int.emod_lt_of_pos (x - a) b_tec
    · simp only [n, Set.mem_setOf_eq]
      use(x - a) / b
      rw [add_assoc]
      --else the next rewrite fails
      rw [Int.emod_add_ediv (x - a) b]
      abel
  · rintro ⟨i, ⟨i_bounds, ai⟩⟩
    intro con
    -- We'll derive a contradiction from basic computations and comparisions
    simp only [n, Set.mem_setOf_eq] at *
    cases' ai with n ndef; cases' con with m mdef
    have target : i = b * (m - n) := by linear_combination -ndef + mdef
    -- rw ndef at mdef,
    -- rw add_assoc at mdef, nth_rewrite_lhs 1 add_comm at mdef,
    -- rw add_left_cancel_iff at mdef,
    -- rw [add_comm, eq_comm] at mdef,
    -- rw ← sub_eq_iff_eq_add at mdef,
    -- rwa [mul_sub, eq_comm],
    -- alternative to the previous line
    apply ltByCases (m - n) 0
    · intro q
      linarith [show i < 0 by rw [target]; apply Linarith.mul_neg q b_tec]
    · intro q; rw [q, MulZeroClass.mul_zero] at target ; linarith
    · intro q
      linarith [show b ≤ i by
          rw [target]
          rw [Int.pos_iff_one_le] at q
          nth_rw 1 [← mul_one b]
          apply mul_le_mul
          apply le_refl; exact q; exact zero_le_one; exact le_of_lt b_tec]

/-- The N sets are closed in our topology -/
theorem n_closed (a b : ℤ) (b_tec : 0 < b) : IsClosed (n a b) := by
  rw [← isOpen_compl_iff]
  rw [n_as_a_complement a b b_tec]
  apply isOpen_biUnion
  simp
  intro i _
  simp only [IsOpen, TopologicalSpace.IsOpen]
  -- unfold the meaning of open in our topology
  right
  intro x xdef
  use b; use b_tec
  intro y ydef
  simp only [n, Set.mem_setOf_eq] at *
  cases' xdef with nx xeq; cases' ydef with ny yeq
  rw [xeq] at yeq
  use nx + ny
  rw [mul_add]; rw [← add_assoc]
  exact yeq

/-- We show that the pathological set {-1,1} isn't open-/
theorem two_units_not_open : ¬bonaFideTopology.IsOpen {(-1 : ℤ), 1} := by
  intro con
  simp [TopologicalSpace.IsOpen] at con
  obtain con | con := con
  · have problem : (-1 : ℤ) ∈ ∅ := by rw [← con]; apply Set.mem_insert
    rw [Set.mem_empty_iff_false] at problem
    exact problem
  · obtain ⟨b, ⟨b_tec, incl⟩⟩ := con.2; clear con
    rw [n] at incl
    have : 1 + b ∈ {x : ℤ | ∃ n : ℤ, x = 1 + b * n} := by
      rw [Set.mem_setOf_eq]; use 1; rw [mul_one b]
    specialize incl this
    obtain incl | incl := incl
    linarith
    simp only [add_right_eq_self, Set.mem_singleton_iff] at incl
    apply lt_irrefl (0 : ℤ); convert b_tec; exact incl.symm

/-- The pathological set {-1,1} complement is the union of
arithmetic progressions with primes as steps.
-/
theorem univ_sdiff_units_as_prime_union : {(-1 : ℤ), (1 : ℤ)}ᶜ = ⋃ p ∈ {x : ℕ | x.Prime}, n 0 p := by
  -- Note : {(-1 : ℤ),1} worked in the previous lemma, and fails here
  ext x;
  constructor
  · intro xuniv
    simp [n] at *
    -- We can disjoin an easy case that will allow us to work with primes later on
    by_cases z : x = 0
    · use 2
      -- any prime works, though 2 has `nat.prime_two`
      constructor
      exact Nat.prime_two
      use 0; rw [MulZeroClass.mul_zero]; exact z
    -- Now, the absolute value of x is ≥ 2, and hence we may use
    -- `int.exists_prime_and_dvd`, which requires the following condition:
    have condition : x.natAbs ≠ 1 := by
      intro con; rw [Int.natAbs_eq_iff] at con
      rw [or_comm] at con
      exact xuniv con
    obtain ⟨p, ⟨p_prime, p_dvd_x⟩⟩ := Int.exists_prime_and_dvd condition
    cases' p_dvd_x with d ddef
    use p.natAbs
    constructor
    · rw [← Int.prime_iff_natAbs_prime]; exact p_prime
    · obtain h | h := Int.natAbs_eq p
      · use d; rwa [← h]
      · use-d; rw [h, neg_mul] at ddef ; rwa [mul_neg]
  · simp [n]
    intro p p_prime d eq
    intro con
    rw [or_comm] at con
    have tec := (@Int.natAbs_eq_iff x 1).mpr
    push_cast at tec
    replace con := tec con; clear tec
    apply_fun Int.natAbs at eq
    rw [con, Int.natAbs_mul, Int.natAbs_ofNat] at eq
    apply Nat.Prime.not_dvd_one p_prime
    use d.natAbs

/-- ### 5th proof of the infinitude of primes

We define a topology on ℤ based on two-way infinite arithmetic progressions.

- In this topology {-1,1} isn't open
- {-1,1}ᶜ is a union of closed sets, indexed by the primes

Hence, if there were finitely many primes, {-1,1}ᶜ would be closed,
contradicting the fact that {-1,1} isn't open.

-/
theorem fifth_proof : {x : ℕ | x.Prime}.Infinite := by
  rw [Set.Infinite]
  intro con
  have pair_as_union := univ_sdiff_units_as_prime_union
  have union_closed : IsClosed (⋃ p ∈ {x : ℕ | x.Prime}, n 0 p) := by
    apply Set.Finite.isClosed_biUnion
    exact con
    intro p pdef
    apply n_closed
    rw [Set.mem_setOf_eq] at pdef
    rw [Nat.cast_pos]
    exact Nat.Prime.pos pdef
  rw [← pair_as_union] at union_closed
  rw [← isOpen_compl_iff] at union_closed
  rw [compl_compl] at union_closed
  exact two_units_not_open union_closed

-- #check fifth_proof
