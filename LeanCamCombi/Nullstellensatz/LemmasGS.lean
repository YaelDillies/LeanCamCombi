/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import Mathlib.Data.MvPolynomial.Supported
import Nullstellensatz.DegreeNew

#align_import nullstellensatz.lemmas_g_S

open Set Function Finsupp AddMonoidAlgebra

open scoped BigOperators

universe u

namespace MvPolynomial

theorem c_mem_supported {R σ : Type _} [CommSemiring R] (s : Set σ) (a : R) : C a ∈ supported R s :=
  mem_supported.2 (by simp)

theorem support_monomial_of_mem_support_of_supported {R σ : Type _} [CommSemiring R]
    {p : MvPolynomial σ R} {i : σ} {s : Set σ} {m : σ →₀ ℕ} (hm : m ∈ p.support)
    (hp : p ∈ supported R s) : ∀ i ∈ m.support, i ∈ s :=
  by
  intro i h
  simp only [Finsupp.mem_support_iff, Ne.def] at h
  by_contra c
  exact
    c
      (mem_of_mem_of_subset (by simpa using (mem_vars i).2 ⟨m, ⟨hm, by simp [h]⟩⟩)
        (mem_supported.1 hp))

theorem support_monomial_of_mem_support_of_supported' {R σ : Type _} [CommSemiring R]
    {p : MvPolynomial σ R} {i : σ} {s : Set σ} {m : σ →₀ ℕ} (hm : m ∈ p.support)
    (hp : p ∈ supported R s) (hi : i ∉ s) : m i = 0 :=
  by
  by_contra c
  exact
    hi
      (mem_of_mem_of_subset (by simpa using (mem_vars i).2 ⟨m, ⟨hm, by simp [c]⟩⟩)
        (mem_supported.1 hp))

theorem eq_single_of_mem_support_of_supported_singleton {R σ : Type _} [CommSemiring R]
    {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} (hm : m ∈ p.support)
    (hp : p ∈ supported R ({i} : Set σ)) : m = single i (m i) :=
  by
  ext j
  by_cases c : i = j
  · simp [c]
  · simp only [c, single_eq_of_ne, Ne.def, not_false_iff]
    apply support_monomial_of_mem_support_of_supported' hm hp
    simp only [mem_singleton_iff]
    by_contra c'
    exact c c'.symm

theorem single_totalDegree_mem_support_of_supported_singleton {R σ : Type _} [CommSemiring R]
    {p : MvPolynomial σ R} {i : σ} (h : p ≠ 0) (hp : p ∈ supported R ({i} : Set σ)) :
    Finsupp.single i p.totalDegree ∈ p.support :=
  by
  rcases exists_max_degree_monomial h with ⟨m, ⟨h, h'⟩⟩
  convert h
  rw [eq_single_of_mem_support_of_supported_singleton h hp]
  congr
  rw [← h', eq_single_of_mem_support_of_supported_singleton h hp, monomial_degree_single]
  simp

theorem dominantMonomialSingleOfSupportedSingleton {R σ : Type _} [CommSemiring R]
    {p : MvPolynomial σ R} {i : σ} (h : p ≠ 0) (hp : p ∈ supported R ({i} : Set σ)) :
    DominantMonomial (Finsupp.single i p.totalDegree) p :=
  by
  rw [dominant_monomial]
  constructor
  · rw [max_degree_monomial]
    constructor
    · exact single_total_degree_mem_support_of_supported_singleton h hp
    · rw [monomial_degree_single]
  · intro t' ht'
    rw [max_degree_monomial] at ht'
    have x := eq_single_of_mem_support_of_supported_singleton ht'.1 hp
    rw [x]
    congr
    rw [x, monomial_degree_single] at ht'
    exact ht'.2

theorem x_sub_c_ne_0 {R σ : Type _} [CommRing R] [DecidableEq σ] [Nontrivial R] (i : σ) (a : R) :
    X i - C a ≠ 0 := by
  rw [nonzero_iff_exists]
  use single i 1
  have h' : ¬0 = single i 1 :=
    by
    -- is this on mathlib?
    suffices t : single i 1 i = 1
    · by_contra h
      simpa [← h] using t
    simp
  have c : coeff (single i 1) (X i - C a) = 1 := by simp [h']
  rw [coeff] at c
  simp [c]

theorem totalDegree_x_sub_c {R σ : Type _} [CommRing R] [DecidableEq σ] [Nontrivial R] (i : σ)
    (a : R) : totalDegree (X i - C a) = 1 :=
  by
  -- this could be a separate lemma called `total_degree_sub_eq_left_of_total_degree_lt`
  rw [sub_eq_add_neg, total_degree_add_eq_left_of_total_degree_lt]
  · simp
  · simp

-- lemmas for g_S
theorem g_S_mem_supported {R σ : Type _} [CommRing R] [Nontrivial R] (S : Finset R) (i : σ) :
    ∏ s in S, (X i - C s) ∈ supported R ({i} : Set σ) :=
  by
  apply (supported R {i}).prod_mem
  intro s hs
  apply (supported R ({i} : Set σ)).sub_mem
  · apply X_mem_supported.2
    · simp
    · exact _inst_2
  · apply C_mem_supported

theorem eval_g_S_eq_zero {R σ : Type _} [CommRing R] [IsDomain R] (S : Finset R) (hS : 0 < S.card)
    (s : σ → R) (i : σ) (h_s : s i ∈ S) : eval s (∏ s in S, (X i - C s)) = 0 := by
  simp [eval_prod, Finset.prod_eq_zero h_s]

theorem g_S_ne_0 {R σ : Type _} [CommRing R] [IsDomain R] [DecidableEq σ] (S : Finset R) (i : σ) :
    ∏ s in S, (X i - C s) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro a ha
  apply X_sub_C_ne_0

theorem totalDegree_g_S {R σ : Type _} [CommRing R] [IsDomain R] [DecidableEq σ] (S : Finset R)
    (i : σ) : totalDegree (∏ s in S, (X i - C s)) = S.card :=
  by
  apply Finset.cons_induction_on S
  · simp
  · clear S
    intro a S haS hind
    rw [Finset.prod_cons, Finset.card_cons, total_degree_mul', hind, add_comm]
    congr
    rw [total_degree_X_sub_C]
    · apply X_sub_C_ne_0
    · apply g_S_ne_0

theorem g_S_monic {R σ : Type _} [CommRing R] [IsDomain R] [DecidableEq σ] (S : Finset R) (i : σ) :
    coeff (single i S.card) (∏ s in S, (X i - C s)) = 1 :=
  by
  apply Finset.cons_induction_on S
  · simp
  · clear S
    intro a S haS hind
    simp only [Finset.prod_cons, sub_mul, coeff_sub, Finset.card_cons, coeff_X_mul', if_true,
      coeff_C_mul, single_eq_same, Pi.add_apply, Nat.succ_ne_zero, Finsupp.mem_support_iff, Ne.def,
      not_false_iff, add_tsub_cancel_right, coe_add, single_add, hind, sub_eq_self, mul_eq_zero]
    right
    rw [← single_add]
    apply coeff_zero_of_degree_greater_than_total_degree
    rw [total_degree_g_S, monomial_degree_single]
    simp

theorem dominantMonomialGS {R σ : Type _} [CommRing R] [IsDomain R] [DecidableEq σ] (S : Finset R)
    (i : σ) : DominantMonomial (Finsupp.single i S.card) (∏ s in S, (X i - C s)) :=
  by
  rw [← total_degree_g_S S i]
  apply dominant_monomial_single_of_supported_singleton
  · apply g_S_ne_0
  · apply g_S_mem_supported

end MvPolynomial
