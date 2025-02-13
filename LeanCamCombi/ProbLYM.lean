/-
Copyright (c) 2024-present Ching-Tsun Chou and Chris Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou and Chris Wong
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.Probability.UniformOn

/-!
# Proof of the LYM inequality using probability theory

This file contains a formalization of the proof of the LYM inequality using
(very elementary) probability theory given in Section 1.2 of Prof. Yufei Zhao's
lecture notes for MIT 18.226:

<https://yufeizhao.com/pm/probmethod_notes.pdf>

A video of Prof. Zhao's lecture on this proof is available on YouTube:

<https://youtu.be/exBXHYl4po8?si=aW8hhJ6zBrvWT1T0>

The proof of Theorem 1.10, Lecture 3 in the Cambridge lecture notes on combinatorics:

<https://github.com/YaelDillies/maths-notes/blob/master/combinatorics.pdf>

is basically the same proof, except with probability theory stripped out.
-/

open BigOperators Fintype Finset Set MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

/-- A numbering is a bijective map from a finite type or set to a Fin type
of the same cardinality.  We cannot use the existing notion of permutations
in mathlib because we need the special property `set_prefix_subset` below. -/

@[reducible]
def Numbering (α : Type*) [Fintype α] := α ≃ Fin (card α)

@[reducible]
def NumberingOn {α : Type*} (s : Finset α) := {x // x ∈ s} ≃ Fin s.card

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem numbering_card : card (Numbering α) = (card α).factorial := by
  exact Fintype.card_equiv (Fintype.equivFinOfCardEq rfl)

omit [Fintype α] in
theorem numbering_on_card (s : Finset α) : card (NumberingOn s) = s.card.factorial := by
  simp only [NumberingOn]
  have h1 : card {x // x ∈ s} = card (Fin s.card) := by simp
  have h2 : {x // x ∈ s} ≃ (Fin s.card) := by exact Fintype.equivOfCardEq h1
  simp [Fintype.card_equiv h2]

/-- `IsPrefix s f` means that the elements of `s` precede the elements of `sᶜ`
in the numbering `f`. -/
def IsPrefix (s : Finset α) (f : Numbering α) :=
  ∀ x, x ∈ s ↔ f x < s.card

omit [DecidableEq α] in
theorem is_prefix_subset {s1 s2 : Finset α} {f : Numbering α}
  (h_s1 : IsPrefix s1 f) (h_s2 : IsPrefix s2 f) (h_card : s1.card ≤ s2.card) : s1 ⊆ s2 := by
  intro a h_as1
  exact (h_s2 a).mpr (lt_of_lt_of_le ((h_s1 a).mp h_as1) h_card)

def is_prefix_equiv (s : Finset α) : {f // IsPrefix s f} ≃ NumberingOn s × NumberingOn sᶜ where
  toFun := fun ⟨f, hf⟩ ↦
    ({
      toFun := fun ⟨x, hx⟩ ↦ ⟨f x, by rwa [← hf x]⟩
      invFun := fun ⟨n, hn⟩ ↦ ⟨f.symm ⟨n, by have := s.card_le_univ; omega⟩, by rw [hf]; simpa⟩
      left_inv := by rintro ⟨x, hx⟩; simp
      right_inv := by rintro ⟨n, hn⟩; simp
    },
    {
      toFun := fun ⟨x, hx⟩ ↦ ⟨f x - s.card, by
        rw [s.mem_compl, hf] at hx
        rw [s.card_compl]
        exact Nat.sub_lt_sub_right (by omega) (by omega)
      ⟩
      invFun := fun ⟨n, hn⟩ ↦ ⟨f.symm ⟨n + s.card, by rw [s.card_compl] at hn; omega⟩,
                               by rw [s.mem_compl, hf]; simp⟩
      left_inv := by
        rintro ⟨x, hx⟩
        rw [s.mem_compl, hf, not_lt] at hx
        simp [Nat.sub_add_cancel hx]
      right_inv := by rintro ⟨n, hn⟩; simp
    })
  invFun := fun (g, g') ↦ ⟨
    {
      toFun := fun x ↦
        if hx : x ∈ s then
          g ⟨x, hx⟩ |>.castLE s.card_le_univ
        else
          g' ⟨x, by simpa⟩ |>.addNat s.card |>.cast (by simp)
      invFun := fun ⟨n, hn⟩ ↦
        if hn' : n < s.card then
          g.symm ⟨n, hn'⟩
        else
          g'.symm ⟨n - s.card, by rw [s.card_compl]; omega⟩
      left_inv := by intro x; by_cases hx : x ∈ s <;> simp [hx]
      right_inv := by
        rintro ⟨n, hn⟩
        by_cases hn' : n < s.card
        · simp [hn']
        · simp [hn']
          split_ifs
          · rename_i h
            have : ∀ x, ↑(g'.symm x) ∉ s := by
              intro x
              simp only [← Finset.mem_compl, Finset.coe_mem]
            exact this _ h |>.elim
          · simp [Nat.sub_add_cancel (not_lt.mp hn')]
    },
    by
      intro x
      constructor
      · intro hx
        simp [hx]
      · by_cases hx : x ∈ s <;> simp [hx]
  ⟩
  left_inv := by
    rintro ⟨f, hf⟩
    ext x
    by_cases hx : x ∈ s
    · simp [hx]
    · rw [hf, not_lt] at hx
      simp [hx]
  right_inv := by
    rintro ⟨g, g'⟩
    simp
    constructor
    · ext x
      simp
    · ext x
      rcases x with ⟨x, hx⟩
      rw [Finset.mem_compl] at hx
      simp [hx]

instance (s : Finset α) :
    DecidablePred fun f ↦ (IsPrefix s f) := by
  intro f ; exact Classical.propDecidable ((fun f ↦ IsPrefix s f) f)

def SetPrefix (s : Finset α) : Finset (Numbering α) :=
  {f | IsPrefix s f}

theorem set_prefix_card (s : Finset α) :
    (SetPrefix s).card = s.card.factorial * (card α - s.card).factorial := by
  have h_eq:= Fintype.card_congr (is_prefix_equiv s)
  rw [Fintype.card_subtype] at h_eq
  rw [SetPrefix, h_eq, Fintype.card_prod, numbering_on_card s, numbering_on_card sᶜ, card_compl]

private lemma aux_1 {k m n : ℕ} (hn : 0 < n) (heq : k * m = n) :
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

instance : MeasurableSpace (Numbering α) := ⊤

theorem set_prefix_count (s : Finset α) :
    count (SetPrefix s).toSet = ↑(s.card.factorial * (card α - s.card).factorial) := by
  rw [← set_prefix_card s, count_apply_finset]

theorem set_prefix_prob (s : Finset α) :
    uniformOn Set.univ (SetPrefix s).toSet = 1 / (card α).choose s.card := by
  rw [uniformOn_univ, set_prefix_count s, numbering_card]
  apply aux_1 (Nat.factorial_pos (card α))
  rw [← mul_assoc]
  exact Nat.choose_mul_factorial_mul_factorial (Finset.card_le_univ s)

theorem set_prefix_disj {s t : Finset α} (h_st : ¬ s ⊆ t) (h_ts : ¬ t ⊆ s) :
    Disjoint (SetPrefix s).toSet (SetPrefix t).toSet := by
  refine Set.disjoint_iff.mpr ?_
  intro p
  simp only [mem_inter_iff, Finset.mem_coe, mem_empty_iff_false, imp_false, not_and]
  simp [SetPrefix]
  intro h_s h_t
  rcases Nat.le_total s.card t.card with h_st' | h_ts'
  · exact h_st (is_prefix_subset h_s h_t h_st')
  · exact h_ts (is_prefix_subset h_t h_s h_ts')

variable {𝓐 : Finset (Finset α)}

theorem antichain_union_prob (h𝓐 : IsAntichain (· ⊆ ·) 𝓐.toSet) :
    uniformOn Set.univ (⋃ s ∈ 𝓐, (SetPrefix s).toSet) =
    ∑ s ∈ 𝓐, uniformOn Set.univ (SetPrefix s).toSet := by
  have hd : 𝓐.toSet.PairwiseDisjoint (fun s ↦ (SetPrefix s).toSet) := by
    intro s h_s t h_t h_ne
    simp only [Function.onFun]
    have h_st := h𝓐 h_s h_t h_ne
    have h_ts := h𝓐 h_t h_s h_ne.symm
    exact set_prefix_disj h_st h_ts
  have hm : ∀ s ∈ 𝓐, MeasurableSet (SetPrefix s).toSet := by
    intro s h_s ; exact trivial
  rw [measure_biUnion_finset hd hm (μ := uniformOn Set.univ)]

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) 𝓐.toSet) :
    ∑ s ∈ 𝓐, ((1 : ENNReal) / (card α).choose s.card) ≤ 1 := by
  have h1 : ∀ s ∈ 𝓐,
      (1 : ENNReal) / (card α).choose s.card = uniformOn Set.univ (SetPrefix s).toSet := by
    intro s h_s
    rw [set_prefix_prob]
  rw [Finset.sum_congr (rfl : 𝓐 = 𝓐) h1, ← antichain_union_prob h𝓐]
  exact prob_le_one

end
