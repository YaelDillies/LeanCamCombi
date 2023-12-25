/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import Nullstellensatz.Lemma21
import Nullstellensatz.ReduceDegree

#align_import nullstellensatz.combinatorial_nullstellensatz

/-!
# Combinatorial Nullstellensatz

In this file we prove the Combinatorial Nullstellensatz.
Our reference is
  N. Alon, Combinatorial Nullstellensatz, Combinatorics, Probability and Computing 8 (1999), 7-29.

## Main results

- `combinatorial_nullstellensatz`: Theorem 1.2 in Alon's paper.
- `combinatorial_nullstellensatz'`: Theorem 1.1 in Alon's paper.
-/


open scoped BigOperators

namespace MvPolynomial

/-- Theorem 1.1 in Alon's paper. -/
theorem combinatorial_nullstellensatz' {R σ : Type _} [CommRing R] [IsDomain R] [Fintype σ]
    [DecidableEq σ] (f : MvPolynomial σ R) (S : σ → Finset R) (hS : ∀ i : σ, 0 < (S i).card)
    (hz : ∀ s : σ → R, (∀ i : σ, s i ∈ S i) → eval s f = 0) :
    ∃ h : σ → MvPolynomial σ R,
      (∀ i : σ, h i = 0 ∨ totalDegree (h i) + (S i).card ≤ totalDegree f) ∧
        f = ∑ i : σ, h i * ∏ s in S i, (X i - C s) :=
  by
  cases' reduce_degree_special_case S hS f with h h_h
  use h
  constructor
  · exact h_h.1
  · rw [← sub_eq_zero]
    apply lemma_2_1 _ S (fun j => h_h.2 j) _
    intro s h_s
    simp only [RingHom.map_sub, hz s h_s, eval_sum, zero_sub, neg_eq_zero, RingHom.map_mul]
    apply Finset.sum_eq_zero
    intro i hi
    simp [eval_g_S_eq_zero (S i) (hS i) s i (h_s i)]

theorem combinatorial_nullstellensatz'' {R σ : Type _} [CommRing R] [IsDomain R] [Fintype σ]
    [DecidableEq σ] (f : MvPolynomial σ R) (t : σ →₀ ℕ) (h_max : MaxDegreeMonomial t f)
    (S : σ → Finset R) (h_card_S : ∀ i : σ, t i + 1 = (S i).card) :
    ∃ s : σ → R, (∀ i : σ, s i ∈ S i) ∧ eval s f ≠ 0 :=
  by
  by_contra hc
  cases'
    combinatorial_nullstellensatz' f S
      (fun i => lt_of_le_of_lt (zero_le (t i)) (by simp [← h_card_S i])) (by simpa using hc) with
    h h1
  clear hc
  suffices h_zero : coeff t (∑ i : σ, h i * ∏ s in S i, (X i - C s)) = 0
  · simpa [h_zero, h1.2] using h_max.1
  simp only [coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases c1 : coeff t (h i * ∏ s : R in S i, (X i - C s)) = 0
  · exact c1
  by_cases c : monomial_degree t > total_degree (h i * ∏ s : R in S i, (X i - C s))
  · exact coeff_zero_of_degree_greater_than_total_degree t _ c
  by_cases c'' : h i = 0
  · simp [c'']
  simpa only [Finsupp.single_eq_same, ← h_card_S, add_le_iff_nonpos_right, le_zero_iff] using
    dominant_monomial_of_factor_is_factor_of_max_degree_monomial (S i) t
      (Finsupp.single i (S i).card) (h i) (∏ s : R in S i, (X i - C s))
      ⟨mem_support_iff.mpr c1, le_antisymm (not_lt.mp c) _⟩ c'' (dominant_monomial_g_S (S i) i) i
  by_cases c' : h i = 0
  · simp [c', MulZeroClass.zero_mul]
  rw [total_degree_mul' c' (g_S_ne_0 (S i) i), total_degree_g_S, h_max.2]
  by_cases hi0 : h i = 0
  · simpa [hi0] using c1
  · exact Or.resolve_left (h1.1 i) hi0

private theorem choose_smaller_sets {R σ : Type _} (S : σ → Finset R) (t : σ →₀ ℕ)
    (h_card_S : ∀ i : σ, t i < (S i).card) :
    ∃ S' : σ → Finset R, (∀ i : σ, S' i ⊆ S i) ∧ ∀ i : σ, (S' i).card = t i + 1 :=
  by
  have t := fun i => Finset.exists_smaller_set (S i) (t i + 1) (h_card_S i)
  convert Classical.skolem.1 t
  ext S'
  rw [forall_and]

/-- Theorem 1.2 in Alon's paper.
-/
theorem combinatorial_nullstellensatz {R σ : Type _} [CommRing R] [IsDomain R] [Fintype σ]
    [DecidableEq σ] (f : MvPolynomial σ R) (t : σ →₀ ℕ) (h_max : MaxDegreeMonomial t f)
    (S : σ → Finset R) (h_card_S : ∀ i : σ, t i < (S i).card) :
    ∃ s : σ → R, (∀ i : σ, s i ∈ S i) ∧ eval s f ≠ 0 :=
  by
  cases' choose_smaller_sets S t h_card_S with S' hS'
  cases' combinatorial_nullstellensatz'' f t h_max S' fun i => (hS'.2 i).symm with s h_s'
  exact ⟨s, ⟨fun i => Finset.mem_of_subset (hS'.1 i) (h_s'.1 i), h_s'.2⟩⟩

end MvPolynomial

