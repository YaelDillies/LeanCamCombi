/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

#align_import book.FormalBook_Ch27_PigeonholeDoublecounting_sequences

/-!
# Pigeon-hole and double counting : Sequences

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 27: "Pigeon-hole and double counting".
In this file, we formalize the section "Sequences".


## Structure

- `erdos_szekeres` :
      In any sequence `a` of `m*n + 1` distinct real numbers,
      there exists an increasing subsequence of length m + 1,
      or a decreasing subsequence of length n + 1, or both.

- `is_increasing_subseq` :
      defines what we mean with "increasing subsequence".

- `is_decreasing_subseq` :
      defines what we mean with "decreasing subsequence".

-/


open Finset

/-- For a sequence `a` and an index `s`, the property `is_increasing_subseq I a s`
says that `I` is a set of indices containing `s`, and on which `a` is
increasing for increasing indices.
-/
def IsIncreasingSubseq (I : Finset ℕ) (a : ℕ → ℝ) (s : ℕ) : Prop :=
  (∀ i ∈ I, ∀ j ∈ I, i < j → a i < a j) ∧ (∀ j ∈ I, s ≤ j) ∧ s ∈ I

/-- For a sequence `a` and an index `s`, the property `is_decreasing_subseq I a s`
says that `I` is a set of indices containing `s`, and on which `a` is
decreasin for increasing indices.
-/
def IsDecreasingSubseq (I : Finset ℕ) (a : ℕ → ℝ) (s : ℕ) : Prop :=
  (∀ i ∈ I, ∀ j ∈ I, i < j → a i > a j) ∧ (∀ j ∈ I, s ≤ j) ∧ s ∈ I

open scoped Classical

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (J «expr ⊆ » I) -/
/-- A technical lemma stating that the set of lengths of increasing
subsequences starting at `i` is nonempty.
-/
theorem lengths_nonempty (I : Finset ℕ) (a : ℕ → ℝ) (i : ℕ) (i_I : i ∈ I) :
    ((range (I.card + 1)).filterₓ fun t =>
        ∃ (J : _) (_ : J ⊆ I), J.card = t ∧ IsIncreasingSubseq J a i).Nonempty :=
  by
  use 1
  rw [mem_filter, mem_range]
  constructor
  · rw [lt_add_iff_pos_left]
    rw [card_pos]
    use i
    exact i_I
  · use singleton i
    constructor
    rw [singleton_subset_iff]
    exact i_I
    constructor
    exact card_singleton i
    -- A one-term-sequence happens to be increasing:
    rw [IsIncreasingSubseq]
    constructor
    intro x x_def y y_def xley
    rw [mem_singleton] at *
    rw [x_def, y_def] at xley
    exfalso
    exact (lt_irrefl i) xley
    constructor
    intro j jsin
    rw [mem_singleton] at jsin
    rw [jsin]
    apply mem_singleton_self

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (J «expr ⊆ » I) -/
/-- For a sequence `a` and an index set `I` acting as universe,
for some `i∈I`, we consider the length of a longest increasing
subsequence starting at `i`, made of indeces of `I` only.
-/
noncomputable def longestIncrSubseqLen (I : Finset ℕ) (a : ℕ → ℝ) (i : ℕ) (i_I : i ∈ I) : ℕ :=
  Finset.max'
    ((range (I.card + 1)).filterₓ fun t =>
      ∃ (J : _) (_ : J ⊆ I), J.card = t ∧ IsIncreasingSubseq J a i)
    (-- Lengths range from 0 to |I|, and we keep those that correspond
      -- to increasing subsequences
      -- We require a proof of non-emptyness for this notion of max
      lengths_nonempty
      I a i i_I)

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (J «expr ⊆ » I) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (J «expr ⊆ » I) -/
/-- We show that when all elements of `a` are distinct, a longest increasing subsequence
may not be extended, in the sense that for two starting indices achieving the
same maximal length, the term indexed by the samller starting point must be
larger then the term indexed by the larger one.
-/
theorem lisl_non_extendable (I : Finset ℕ) (a : ℕ → ℝ) (i j : ℕ) (i_I : i ∈ I) (j_I : j ∈ I)
    (distinct : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → a i ≠ a j)
    (h : longestIncrSubseqLen I a i i_I = longestIncrSubseqLen I a j j_I) (wlog : j < i) :
    a j > a i := by
  by_contra! con
  replace con :=
    show a j < a i by
      apply lt_of_le_of_ne Con
      apply distinct j j_I i i_I
      exact ne_of_lt wlog
  -- We find a longest increasing subsequence satrting at i
  have tec1 :
    longestIncrSubseqLen I a i i_I ∈
      (range (I.card + 1)).filterₓ fun t =>
        ∃ (J : _) (_ : J ⊆ I), J.card = t ∧ IsIncreasingSubseq J a i :=
    by
    rw [longestIncrSubseqLen]
    apply max'_mem
  rw [mem_filter] at tec1
  rcases tec1 with ⟨ran, index_seq, index_sub, size, last⟩
  rw [IsIncreasingSubseq] at *
  rcases last with ⟨index_seq_inc, index_seq_imin, index_seq_iin⟩
  -- Extending it by pre-pending j results in an increasing subsequence starting at j
  have extend : IsIncreasingSubseq (insert j index_seq) a j :=
    by
    constructor
    -- It's increasing:
    · intro x xdef y ydef xly
      rw [mem_insert] at *
      cases' xdef with xeqj x_index
      cases' ydef with yeqj y_index
      · rw [xeqj, yeqj] at xly
        exfalso
        exact (lt_irrefl j) xly
      · specialize index_seq_imin y y_index
        rw [xeqj]
        rw [le_iff_eq_or_lt] at index_seq_imin
        cases index_seq_imin
        rw [← index_seq_imin]
        exact Con
        specialize index_seq_inc i index_seq_iin y y_index index_seq_imin
        exact lt_trans Con index_seq_inc
      cases' ydef with yeqj y_index
      · exfalso
        specialize index_seq_imin x x_index
        apply lt_irrefl j
        rw [yeqj] at xly
        apply lt_trans wlog
        exact lt_of_le_of_lt index_seq_imin xly
      · exact index_seq_inc x x_index y y_index xly
    constructor
    -- j is a lower boud to the indices
    · intro x xdef
      rw [mem_insert] at xdef
      cases xdef
      rw [xdef]
      apply le_of_lt
      apply lt_of_lt_of_le wlog
      exact index_seq_imin x xdef
    -- j is a member
    apply mem_insert_self
  -- To derive a contradiction with the length of this new sequence,
  -- we bring it in form to be considered in the set of lengths we
  -- took a maximum over.
  have contra_pre :
    (insert j index_seq).card ∈
      (range (I.card + 1)).filterₓ fun t =>
        ∃ (J : _) (_ : J ⊆ I), J.card = t ∧ IsIncreasingSubseq J a j :=
    by
    rw [mem_filter]
    constructor
    · rw [mem_range]
      apply lt_of_le_of_lt (card_insert_le j index_seq)
      rw [add_lt_add_iff_right]
      apply card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      exact index_sub
      by_contra C
      rw [← C] at j_I
      apply not_le_of_lt wlog
      exact index_seq_imin j j_I
    use insert j index_seq
    constructor
    · rw [insert_subset]
      exact ⟨j_I, index_sub⟩
    constructor
    rfl
    exact extend
  -- We may now use the maximum to derive the non-sensical bound:
  have contra_pre_2 : (insert j index_seq).card ≤ longestIncrSubseqLen I a j j_I :=
    by
    rw [longestIncrSubseqLen]
    apply le_max'
    exact contra_pre
  clear contra_pre
  rw [card_insert_of_not_mem _] at contra_pre_2
  swap
  · by_contra C
    apply not_le_of_lt wlog
    exact index_seq_imin j C
  rw [size] at contra_pre_2
  apply not_lt_of_le contra_pre_2
  -- nat.lt_succ missing
  linarith

/-- A technical lemma we left out of the main proof to shorten it.
A (longest) increasing subsequence staring at i has at least length 1.
-/
theorem lisl_pos (I : Finset ℕ) (a : ℕ → ℝ) (i : ℕ) (i_I : i ∈ I) :
    1 ≤ longestIncrSubseqLen I a i i_I :=
  by
  rw [longestIncrSubseqLen]
  apply le_max'
  rw [mem_filter, mem_range]
  -- From here, the proof is the same as that used in `lengths_nonempty`.
  constructor
  · rw [lt_add_iff_pos_left]
    rw [card_pos]
    use i
    exact i_I
  · use singleton i
    constructor
    rw [singleton_subset_iff]
    exact i_I
    constructor
    exact card_singleton i
    rw [IsIncreasingSubseq]
    constructor
    intro x x_def y y_def xley
    rw [mem_singleton] at *
    rw [x_def, y_def] at xley
    exfalso
    exact (lt_irrefl i) xley
    constructor
    intro j jsin
    rw [mem_singleton] at jsin
    rw [jsin]
    apply mem_singleton_self

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (I «expr ⊆ » range[finset.range] «expr + »(«expr * »(m, n), 1)) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (I «expr ⊆ » range[finset.range] «expr + »(«expr * »(m, n), 1)) -/
/-- ### Claim

In any sequence `a` of `m*n + 1` distinct real numbers,
there exists an increasing subsequence of length m + 1,
or a decreasing subsequence of length n + 1, or both.
-/
theorem erdos_szekeres (n m : ℕ) (n_pos : 0 < n) (m_pos : 0 < m) (a : ℕ → ℝ)
    (distinct : ∀ i ∈ range (m * n + 1), ∀ j ∈ range (m * n + 1), i ≠ j → a i ≠ a j) :
    (∃ i ∈ range (m * n + 1),
        ∃ (I : _) (_ : I ⊆ range (m * n + 1)), IsIncreasingSubseq I a i ∧ I.card ≥ m + 1) ∨
      ∃ i ∈ range (m * n + 1),
        ∃ (I : _) (_ : I ⊆ range (m * n + 1)), IsDecreasingSubseq I a i ∧ I.card ≥ n + 1 :=
  by
  -- If one weren't the case, we must get the other
  rw [Classical.or_iff_not_imp_left]
  intro d
  push_neg at d
  -- This will map pigeon to holes with the following map.
  -- We must extend it, as `longest_incr_subseq_len` isn't defined
  -- outside of `range (m * n + 1)`.
  set f := fun i =>
    if h : i ∈ range (m * n + 1) then longestIncrSubseqLen (range (m * n + 1)) a i h else 0
  have map_cond : ∀ a, a ∈ range (m * n + 1) → f a ∈ Icc 1 m :=
    by
    intro s s_range
    rw [mem_Icc]
    dsimp [f]
    rw [dif_pos s_range]
    constructor
    exact lisl_pos (range (m * n + 1)) a s s_range
    specialize d s s_range
    dsimp [longestIncrSubseqLen]
    apply max'_le
    intro y ydef
    rw [mem_filter] at ydef
    obtain ⟨I, Idef, Icard, Iinc⟩ := ydef.2
    rw [← Nat.lt_add_one_iff, ← Icard]
    exact d I Idef Iinc
  have size_cond : (Icc 1 m).card * n < (range (m * n + 1)).card :=
    by
    rw [Nat.card_Icc, card_range]
    rw [Nat.add_sub_cancel]
    simp only [lt_add_iff_pos_right, eq_self_iff_true, Nat.lt_one_iff]
  obtain ⟨j, j_def, ineq⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to map_cond size_cond
  -- a generalized version of the pigeonhole principle
  -- Our candidate for the subsequence
  set I := (range (m * n + 1)).filterₓ fun x => f x = j with Idef
  -- More notation and quick facts
  have tec_1 : I.nonempty := by
    rw [← card_pos]
    rw [Idef]
    exact lt_trans n_pos ineq
  have tec_2 : I ⊆ range (m * n + 1) := by
    rw [Idef]
    apply filter_subset
  -- Our candidate for starting the subsequence
  set i := Finset.min' I tec_1 with i_def
  use i
  constructor
  · apply tec_2
    rw [i_def]
    apply min'_mem
  use I
  constructor
  exact tec_2
  constructor
  · dsimp [IsDecreasingSubseq]
    constructor
    · -- For `x < y`, if `a x < a y`, we could extend the longest increasing
      -- subsequence starting at `x` by that of `y`, which would contradict
      -- maximality.
      intro x x_I y y_I xly
      apply lisl_non_extendable (range (m * n + 1)) a y x (tec_2 y_I) (tec_2 x_I) distinct
      swap
      exact xly
      --rw Idef at x_I, rw Idef at y_I, --truns out to be unnecessary
      rw [mem_filter] at *
      dsimp [f] at x_I
      dsimp [f] at y_I
      --rw (dif_pos x_I_1.1) at x_I_1, --plausible but makes 4 goals...
      rw [show longestIncrSubseqLen (range (m * n + 1)) a y (tec_2 y_I) = j
          by
          cases' y_I_1 with yIl yIr
          rw [dif_pos yIl] at yIr
          exact yIr]
      rw [show longestIncrSubseqLen (range (m * n + 1)) a x (tec_2 x_I) = j
          by
          cases' x_I_1 with xIl xIr
          rw [dif_pos xIl] at xIr
          exact xIr]
    constructor
    · rw [i_def]
      apply min'_le
    · rw [i_def]
      apply min'_mem
  -- The pigeonhole principles boudn on the size allows us to conclude:
  · rw [Idef]
    rw [GE.ge]
    rw [Nat.add_one_le_iff]
    exact ineq
