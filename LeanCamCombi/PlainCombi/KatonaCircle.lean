/-
Copyright (c) 2024 Ching-Tsun Chou, Chris Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Chris Wong
-/
import LeanCamCombi.Mathlib.Data.Fintype.Card
import LeanCamCombi.PlainCombi.ProbLYM
import Mathlib.Probability.UniformOn

/-!
# The LYM inequality using probability theory

This file proves the LYM inequality using (very elementary) probability theory.

## References

This proof formalizes Section 1.2 of Prof. Yufei Zhao's lecture notes for MIT 18.226:

<https://yufeizhao.com/pm/probmethod_notes.pdf>

A video of Prof. Zhao's lecture is available on YouTube:

<https://youtu.be/exBXHYl4po8>

The proof of Theorem 1.10, Lecture 3 in the Cambridge lecture notes on combinatorics:

<https://github.com/YaelDillies/maths-notes/blob/master/combinatorics.pdf>

is basically the same proof, except without using probability theory.
-/

open BigOperators Fintype Finset Set MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

private lemma auxLemma {k m n : ℕ} (hn : 0 < n) (heq : k * m = n) :
    (↑ m : ENNReal) / (↑ n : ENNReal) = 1 / (↑ k : ENNReal) := by
  -- The following proof is due to Aaron Liu.
  subst heq
  have hm : m ≠ 0 := by rintro rfl ; simp at hn
  have hk : k ≠ 0 := by rintro rfl ; simp at hn
  refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_
  · intro h
    apply_fun ENNReal.toReal at h
    simp [hm, hk] at h
  · intro h
    apply_fun ENNReal.toReal at h
    simp [hk] at h
  · field_simp
    ring

variable {α : Type*} [Fintype α] [DecidableEq α]

instance : MeasurableSpace (Numbering α) := ⊤

theorem count_PrefixedNumbering (s : Finset α) :
    count (PrefixedNumbering s).toSet = ↑((#s).factorial * (card α - #s).factorial) := by
  rw [← card_PrefixedNumbering s, count_apply_finset]

theorem prob_PrefixedNumbering (s : Finset α) :
    uniformOn Set.univ (PrefixedNumbering s).toSet = 1 / (card α).choose #s := by
  rw [uniformOn_univ, count_PrefixedNumbering s, card_Numbering]
  apply auxLemma (Nat.factorial_pos (card α))
  rw [← mul_assoc]
  exact Nat.choose_mul_factorial_mul_factorial (Finset.card_le_univ s)

theorem disj_PrefixedNumbering {s t : Finset α} (h_st : ¬ s ⊆ t) (h_ts : ¬ t ⊆ s) :
    Disjoint (PrefixedNumbering s).toSet (PrefixedNumbering t).toSet := by
  refine Set.disjoint_iff.mpr ?_
  intro p
  simp only [mem_inter_iff, Finset.mem_coe, mem_empty_iff_false, imp_false, not_and]
  simp [PrefixedNumbering]
  intro h_s h_t
  rcases Nat.le_total #s t.card with h_st' | h_ts'
  · exact h_st (subset_IsPrefix_IsPrefix h_s h_t h_st')
  · exact h_ts (subset_IsPrefix_IsPrefix h_t h_s h_ts')

variable {𝓐 : Finset (Finset α)}

theorem prob_biUnion_antichain (h𝓐 : IsAntichain (· ⊆ ·) 𝓐.toSet) :
    uniformOn Set.univ (⋃ s ∈ 𝓐, (PrefixedNumbering s).toSet) =
    ∑ s ∈ 𝓐, uniformOn Set.univ (PrefixedNumbering s).toSet := by
  have hd : 𝓐.toSet.PairwiseDisjoint (fun s ↦ (PrefixedNumbering s).toSet) := by
    intro s h_s t h_t h_ne
    simp only [Function.onFun]
    have h_st := h𝓐 h_s h_t h_ne
    have h_ts := h𝓐 h_t h_s h_ne.symm
    exact disj_PrefixedNumbering h_st h_ts
  have hm : ∀ s ∈ 𝓐, MeasurableSet (PrefixedNumbering s).toSet := by
    intro s h_s ; exact trivial
  rw [measure_biUnion_finset hd hm (μ := uniformOn Set.univ)]

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) 𝓐.toSet) :
    ∑ s ∈ 𝓐, ((1 : ENNReal) / (card α).choose #s) ≤ 1 := by
  have h1 s (hs : s ∈ 𝓐) :
      (1 : ENNReal) / (card α).choose #s = uniformOn Set.univ (PrefixedNumbering s).toSet := by
    rw [prob_PrefixedNumbering]
  rw [Finset.sum_congr (rfl : 𝓐 = 𝓐) h1, ← prob_biUnion_antichain h𝓐]
  exact prob_le_one

end
