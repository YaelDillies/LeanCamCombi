/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Data.Polynomial.RingDivision

#align_import nullstellensatz.lemma_2_1

/-
# Lemma 2.1

## Main results

- `lemma_2_1`: Let F be a field and f ∈ F[x₀,…,xₙ]. Suppose that for 0 ≤ i ≤ n,
  the degree of f in xᵢ is at most tᵢ. Let S₀,…,Sₙ ⊆ F be subsets such that tᵢ < |Sᵢ|.
  Suppose that f(s₀,…,sₙ) = 0 for each (s₀,…,sₙ) ∈ S₀ × … × Sₙ. Then f = 0.

  This is Lemma 2.1 in Alon's paper "Combinatorial Nullstellensatz".
-/
/-
# Lemma 2.1

## Main results

- `lemma_2_1`: Let F be a field and f ∈ F[x₀,…,xₙ]. Suppose that for 0 ≤ i ≤ n,
  the degree of f in xᵢ is at most tᵢ. Let S₀,…,Sₙ ⊆ F be subsets such that tᵢ < |Sᵢ|.
  Suppose that f(s₀,…,sₙ) = 0 for each (s₀,…,sₙ) ∈ S₀ × … × Sₙ. Then f = 0.

  This is Lemma 2.1 in Alon's paper "Combinatorial Nullstellensatz".
-/
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MvPolynomial

private theorem lemma_2_1_fin_n {n : ℕ} {R : Type _} [CommRing R] [IsDomain R]
    (f : MvPolynomial (Fin n) R) (S : Fin n → Finset R)
    (hS : ∀ i : Fin n, degreeOf i f < (S i).card)
    (hz : ∀ s : Fin n → R, (∀ i : Fin n, s i ∈ S i) → eval s f = 0) : f = 0 :=
  by
  induction' n with n hn
  simp only [forall_const] at hz
  apply (RingEquiv.map_eq_zero_iff (is_empty_ring_equiv R (Fin 0))).1
  simp only [is_empty_ring_equiv_apply]
  simpa using hz fin.is_empty.elim
  apply (RingEquiv.map_eq_zero_iff ↑(finSuccEquiv R n)).1 ∘ Polynomial.ext_iff.2
  intro i
  rw [← Polynomial.coeff_zero i]
  apply hn (Polynomial.coeff ((finSuccEquiv R n) f) i)
  exact fun j => lt_of_le_of_lt (degree_of_coeff_fin_succ_equiv f j i) (hS j.succ)
  intro s hs
  rw [← coeff_eval_eq_eval_coeff]
  suffices h : Polynomial.map (eval s) (finSuccEquiv R n f) = 0
  · rw [h]
    simp
  by_contra c1
  suffices h1 : (S 0).val ⊆ (Polynomial.map (eval fun i : Fin n => s i) (finSuccEquiv R n f)).roots
  · simpa using lt_of_le_of_lt ((Polynomial.card_le_degree_of_subset_roots h1).trans _) (hS 0)
    rw [← nat_degree_fin_succ_equiv f]
    exact
      Polynomial.natDegree_le_natDegree (Polynomial.degree_mono (Polynomial.support_map_subset _ _))
  suffices h0 :
    ∀ s' : Fin n → R,
      (∀ i : Fin n, s' i ∈ S i.succ) →
        ∀ y : R, y ∈ S 0 → Polynomial.eval y (Polynomial.map (eval s') ((finSuccEquiv R n) f)) = 0
  · rw [Multiset.subset_iff]
    intro x hx
    rw [Polynomial.mem_roots c1]
    simpa using h0 _ hs x hx
  intro s' hs' y hy
  rw [← eval_eq_eval_mv_eval', hz]
  intro i
  by_cases c : i ≠ 0
  · rw [← Fin.succ_pred i c, Fin.cons_succ]
    exact hs' (Fin.pred i c)
  · rwa [Classical.not_not.1 c, Fin.cons_zero]

/-- Lemma 2.1 in Alon's "Combinatorial Nullstellensatz" paper. -/
theorem lemma_2_1 {R σ : Type _} [CommRing R] [IsDomain R] [Fintype σ] (f : MvPolynomial σ R)
    (S : σ → Finset R) (hS : ∀ i : σ, degreeOf i f < (S i).card)
    (hz : ∀ s : σ → R, (∀ i : σ, s i ∈ S i) → eval s f = 0) : f = 0 :=
  by
  rcases exists_fin_rename f with ⟨n, ⟨ψ, ⟨hψ, ⟨g, hg⟩⟩⟩⟩
  rw [hg]
  rw [hg] at hS
  rw [hg] at hz
  clear hg f
  have h_S_nonempty : ∀ i, ∃ x, x ∈ S i := by
    intro i
    apply Multiset.card_pos_iff_exists_mem.1
    convert lt_of_le_of_lt (zero_le _) (hS i)
  have hs0 : ∃ s0 : σ → R, ∀ i : σ, s0 i ∈ S i := by apply Classical.skolem.1 h_S_nonempty
  cases' hs0 with s0 hs0
  by_cases c : Nonempty (Fin n)
  · have hS' : ∀ i : Fin n, degree_of i g < ((S ∘ ψ) i).card :=
      by
      intro i
      convert hS (ψ i)
      rw [degree_of_rename_of_injective hψ i]
    suffices hz' : ∀ s : Fin n → R, (∀ i : Fin n, s i ∈ (S ∘ ψ) i) → eval s g = 0
    · simp [lemma_2_1_fin_n g (S ∘ ψ) hS' hz']
    intro s' h
    let φ := @Function.invFun (Fin n) σ c ψ
    have φ_left_inv := @Function.leftInverse_invFun (Fin n) σ c ψ hψ
    let s : σ → R := fun i => if h : ∃ j : Fin n, ψ j = i then (s' ∘ φ) i else s0 i
    have hs' : s' = s ∘ ψ := by
      ext
      have hx : ∃ j, ψ j = ψ x := ⟨x, by rfl⟩
      simp only [Function.comp_apply, s, hx, dif_pos, φ, φ_left_inv x]
    suffices hs : ∀ i : σ, s i ∈ S i
    · rw [hs']
      convert hz s hs
      simp only [eval, eval₂_hom_rename]
    intro i
    by_cases ch : ∃ j : Fin n, ψ j = i
    · simp only [s, dite_eq_ite, Function.comp_apply, if_pos, ch, φ]
      cases' ch with j hj
      simpa [← hj, φ_left_inv j] using h j
    · simpa only [s, dite_eq_ite, if_neg, ch, not_false_iff] using hs0 i
  · simp only [not_nonempty_iff] at c
    cases' @C_surjective R _ (Fin n) c g with a ha
    simp only [← ha, rename_C] at hz
    have t := hz s0 hs0
    rw [eval_C] at t
    simp [← ha, rename_C, t]

end MvPolynomial
