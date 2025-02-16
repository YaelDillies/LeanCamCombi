/-
Copyright (c) 2024 Ching-Tsun Chou, Chris Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Chris Wong
-/
import LeanCamCombi.Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
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

/-- A numbering is a bijective map from a finite type or set to a Fin type
of the same cardinality.  We cannot use the existing notion of permutations
in mathlib because we need the special property `set_prefix_subset` below. -/

@[reducible]
def Numbering (α : Type*) [Fintype α] := α ≃ Fin (card α)

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_Numbering : card (Numbering α) = (card α).factorial := by
  exact Fintype.card_equiv (Fintype.equivFinOfCardEq rfl)

/-- `IsPrefix s f` means that the elements of `s` precede the elements of `sᶜ`
in the numbering `f`. -/
def IsPrefix (s : Finset α) (f : Numbering α) :=
  ∀ x, x ∈ s ↔ f x < #s

omit [DecidableEq α] in
theorem subset_IsPrefix_IsPrefix {s1 s2 : Finset α} {f : Numbering α}
  (h_s1 : IsPrefix s1 f) (h_s2 : IsPrefix s2 f) (h_card : s1.card ≤ s2.card) : s1 ⊆ s2 := by
  intro a h_as1
  exact (h_s2 a).mpr (lt_of_lt_of_le ((h_s1 a).mp h_as1) h_card)

def equiv_IsPrefix_Numbering2 (s : Finset α) :
    {f // IsPrefix s f} ≃ Numbering s × Numbering ↑(sᶜ) where
  toFun := fun ⟨f, hf⟩ ↦
    { fst.toFun x := ⟨f x, by simp [← hf x]⟩
      fst.invFun n :=
        ⟨f.symm ⟨n, n.2.trans_le <| by simpa using s.card_le_univ⟩, by rw [hf]; simpa using n.2⟩
      fst.left_inv x := by simp
      fst.right_inv n := by simp
      snd.toFun x := ⟨f x - #s, by
        have := (hf x).not.1 (Finset.mem_compl.1 x.2)
        simp at this ⊢
        omega⟩
      snd.invFun n :=
        ⟨f.symm ⟨n + #s, Nat.add_lt_of_lt_sub <| by simpa using n.2⟩, by rw [s.mem_compl, hf]; simp⟩
      snd.left_inv := by
        rintro ⟨x, hx⟩
        rw [s.mem_compl, hf, not_lt] at hx
        simp [Nat.sub_add_cancel hx]
      snd.right_inv := by rintro ⟨n, hn⟩; simp }
  invFun := fun (g, g') ↦
    { val.toFun x :=
        if hx : x ∈ s then
          g ⟨x, hx⟩ |>.castLE Fintype.card_subtype_le'
        else
          g' ⟨x, by simpa⟩ |>.addNat #s |>.cast (by simp [card_le_univ])
      val.invFun n :=
        if hn : n < #s then
          g.symm ⟨n, by simpa using hn⟩
        else
          g'.symm ⟨n - #s, by simp; omega⟩
      val.left_inv x := by
        by_cases hx : x ∈ s
        · have : g ⟨x, hx⟩ < #s := by simpa using (g ⟨x, hx⟩).2
          simp [hx, this]
        · simp [hx, Equiv.symm_apply_eq]
      val.right_inv n := by
        obtain hns | hsn := lt_or_le n.1 #s
        · simp [hns]
        · simp [hsn.not_lt, hsn, dif_neg (mem_compl.1 <| Subtype.prop _), Fin.ext_iff,
            Fintype.card_subtype_le']
      property x := by
        constructor
        · intro hx
          simpa [hx, -Fin.is_lt] using (g _).is_lt
        · by_cases hx : x ∈ s <;> simp [hx] }
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

def PrefixedNumbering (s : Finset α) : Finset (Numbering α) :=
  {f | IsPrefix s f}

theorem card_PrefixedNumbering (s : Finset α) :
    (PrefixedNumbering s).card = (#s).factorial * (card α - #s).factorial := by
  have h_eq:= Fintype.card_congr (equiv_IsPrefix_Numbering2 s)
  rw [Fintype.card_subtype] at h_eq
  simp [PrefixedNumbering, h_eq, card_Numbering]

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
