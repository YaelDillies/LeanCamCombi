/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import Nullstellensatz.DegreeNew
import Nullstellensatz.LemmasGS

#align_import nullstellensatz.reduce_degree

/-
# Reduce degree

## Main results

- `is_reduced`: A mv_polynomial f is reduced with respect to m : σ →₀ ℕ if no monomial m' in the
  support of f satisfies m ≤ m'.

- `reduce_degree`: Let R be a integral domain and let f ∈ R[xₛ] be a multivariable polynomial.
   Suppose we are given a finite number of nonconstant polynomials gᵢ ∈ R[xₛ] each having a
   dominant monomial mᵢ with coefficient 1. Then we can find polynomials hᵢ ∈ R[xₛ] such that:
  (i) For each i, either hᵢ = 0 or deg hᵢ + deg gᵢ ≤ deg f.
  (ii) For each i, f - ∑ j : τ, hⱼ gⱼ is reduced with respect to mᵢ.

- `reduce_degree_special_case`: Let R be a integral domain and Sᵢ be finite nonempty subsets of R,
   defined for i ∈ {0, … , n - 1}. Let f ∈ R[x₀, … xₙ]. Let gᵢ = ∏ (xᵢ - s)
   where the product is taken over s ∈ Sᵢ.Then there are polynomials
   hᵢ ∈ F[x₀, … xₙ] such that:
   (i) For each i, either hᵢ = 0 or deg hᵢ + |Sᵢ| ≤ deg f.
  (ii) For each j, degⱼ (f - ∑ᵢ hᵢ gᵢ) < |Sⱼ|.

  This corresponds to the following paragraph in the proof of Theorem 1.1 in Alon's
  "Combinatorial Nullstellensatz" paper:
  'Let \bar{f} be the polynomial obtained by writing f as a linear combination of monomials and replacing,
  repeatedly, each occurrence of x ^ f_i (for 1 ≤ i ≤ n), where f_i > t_i, by a linear combination
  of smaller powers of x_i, using the relations g_i = ∏ s in (S i), (X i - C s) = 0. The resulting
  polynomial \bar{f} is clearly of degree at most t_i in x_i, for each 1 ≤ i ≤ n, and is obtained from
  f by subtracting from it products of the form h_i * g_i, where the degree of each polynomial
  h_i ∈ F[x_1 , ... , x_n] does not exceed deg(f) − deg(g_i)'.

-/
/-
# Reduce degree

## Main results

- `is_reduced`: A mv_polynomial f is reduced with respect to m : σ →₀ ℕ if no monomial m' in the
  support of f satisfies m ≤ m'.

- `reduce_degree`: Let R be a integral domain and let f ∈ R[xₛ] be a multivariable polynomial.
   Suppose we are given a finite number of nonconstant polynomials gᵢ ∈ R[xₛ] each having a
   dominant monomial mᵢ with coefficient 1. Then we can find polynomials hᵢ ∈ R[xₛ] such that:
  (i) For each i, either hᵢ = 0 or deg hᵢ + deg gᵢ ≤ deg f.
  (ii) For each i, f - ∑ j : τ, hⱼ gⱼ is reduced with respect to mᵢ.

- `reduce_degree_special_case`: Let R be a integral domain and Sᵢ be finite nonempty subsets of R,
   defined for i ∈ {0, … , n - 1}. Let f ∈ R[x₀, … xₙ]. Let gᵢ = ∏ (xᵢ - s)
   where the product is taken over s ∈ Sᵢ.Then there are polynomials
   hᵢ ∈ F[x₀, … xₙ] such that:
   (i) For each i, either hᵢ = 0 or deg hᵢ + |Sᵢ| ≤ deg f.
  (ii) For each j, degⱼ (f - ∑ᵢ hᵢ gᵢ) < |Sⱼ|.

  This corresponds to the following paragraph in the proof of Theorem 1.1 in Alon's
  "Combinatorial Nullstellensatz" paper:
  'Let \bar{f} be the polynomial obtained by writing f as a linear combination of monomials and replacing,
  repeatedly, each occurrence of x ^ f_i (for 1 ≤ i ≤ n), where f_i > t_i, by a linear combination
  of smaller powers of x_i, using the relations g_i = ∏ s in (S i), (X i - C s) = 0. The resulting
  polynomial \bar{f} is clearly of degree at most t_i in x_i, for each 1 ≤ i ≤ n, and is obtained from
  f by subtracting from it products of the form h_i * g_i, where the degree of each polynomial
  h_i ∈ F[x_1 , ... , x_n] does not exceed deg(f) − deg(g_i)'.

-/
universe u

open Set Function Finsupp AddMonoidAlgebra

open scoped BigOperators

namespace MvPolynomial

open Set Function Finsupp AddMonoidAlgebra

attribute [local instance] Classical.propDecidable

def IsReduced {R σ : Type _} [CommRing R] (f : MvPolynomial σ R) (m : σ →₀ ℕ) : Prop :=
  ∀ m' ∈ f.support, ¬m ≤ m'

-- would ∀ m', m ≤ m' → m ∉ f.support be better?
theorem isReducedAdd {R σ : Type _} [CommRing R] {f g : MvPolynomial σ R} {m : σ →₀ ℕ}
    (hf : IsReduced f m) (hg : IsReduced g m) : IsReduced (f + g) m :=
  by
  rw [IsReduced]
  intro m' hm'
  have t := support_add hm'
  simp only [Finset.mem_union] at t 
  cases t
  · exact hf m' t
  · exact hg m' t

private def M {R σ τ : Type _} [CommRing R] [IsDomain R] [Fintype τ] {g : τ → MvPolynomial σ R}
    {m : τ → σ →₀ ℕ} (hm : ∀ i : τ, DominantMonomial (m i) (g i))
    (h0 : ∀ i : τ, 0 < totalDegree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) :
    MvPolynomial σ R → Prop := fun f =>
  ∃ h : τ → MvPolynomial σ R,
    (∀ i : τ, h i = 0 ∨ totalDegree (h i) + totalDegree (g i) ≤ totalDegree f) ∧
      ∀ i : τ, IsReduced (f - ∑ j : τ, h j * g j) (m i)

private theorem h_add_weak_aux_comp {R σ τ : Type _} [CommRing R] [Fintype τ]
    (g : τ → MvPolynomial σ R) (p q : MvPolynomial σ R) (h1 h2 : τ → MvPolynomial σ R) :
    p + q - ∑ i : τ, (h1 + h2) i * g i = p - ∑ i : τ, h1 i * g i + (q - ∑ i : τ, h2 i * g i) :=
  calc
    p + q - ∑ i : τ, (h1 + h2) i * g i = p + q - ∑ i : τ, (h1 i + h2 i) * g i := by simp
    _ = p + q - ∑ i : τ, (h1 i * g i + h2 i * g i) :=
      by
      simp only [sub_right_inj]
      congr
      ext
      congr
      rw [add_mul]
    _ = p + q - (∑ i : τ, h1 i * g i + ∑ i : τ, h2 i * g i) := by
      simp only [sub_right_inj, Finset.sum_add_distrib]
    _ = p - ∑ i : τ, h1 i * g i + (q - ∑ i : τ, h2 i * g i) := by
      rw [← add_sub_assoc, ← sub_sub (p + q), sub_left_inj, sub_add_eq_add_sub]

private theorem reduce_degree_h_add_weak {R σ τ : Type _} [CommRing R] [IsDomain R] [Fintype τ]
    {g : τ → MvPolynomial σ R} {m : τ → σ →₀ ℕ} (hm : ∀ i : τ, DominantMonomial (m i) (g i))
    (h0 : ∀ i : τ, 0 < totalDegree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) (a : σ →₀ ℕ)
    (b : R) (f : MvPolynomial σ R) (ha : a ∉ f.support) (hb : b ≠ 0) (Mf : M hm h0 hmonic f)
    (Mab : M hm h0 hmonic (monomial a b)) : M hm h0 hmonic (monomial a b + f) :=
  by
  cases' Mf with hf h_hf
  cases' Mab with hab h_hab
  use hab + hf
  constructor
  · intro i
    simp only [total_degree_add_monomial f a b ha hb, Pi.add_apply]
    by_cases c : hab i = 0
    · by_cases c' : hf i = 0
      · simp [c, c']
      · right
        simp only [c, zero_add, Pi.add_apply]
        exact
          (Or.resolve_left (h_hf.1 i) c').trans
            (le_max_right (total_degree (monomial a b)) (total_degree f))
    · by_cases c' : hf i = 0
      · right
        rw [c']
        simp only [add_zero]
        exact
          (Or.resolve_left (h_hab.1 i) c).trans
            (le_max_left (total_degree (single a b)) (total_degree f))
      · right
        apply
          le_trans _ (max_le_max (Or.resolve_left (h_hab.1 i) c) (Or.resolve_left (h_hf.1 i) c'))
        rw [max_add_add_right]
        apply add_le_add_right
        apply total_degree_add
  · intro i
    rw [h_add_weak_aux_comp]
    exact is_reduced_add (h_hab.2 i) (h_hf.2 i)

private theorem total_degree_p_aux {σ : Type _} {m m' a : σ →₀ ℕ} (h_m_le_a : m ≤ a)
    (h : monomialDegree a ≤ monomialDegree m') (c : a - m ≤ m')
    (t :
      monomialDegree (m' - (a - m)) ≤ monomialDegree m ∧
        (monomialDegree (m' - (a - m)) = monomialDegree m → m = m' - (a - m))) :
    a = m' :=
  by
  have h' : m' - (a - m) = m + m' - a := by
    rw [add_comm]
    exact monomial_lemma_1 h_m_le_a c
  rw [h'] at t 
  clear h'
  suffices h1 : monomial_degree (m + m' - a) = monomial_degree m
  · ext i
    zify
    have t'' : (m i : ℤ) = m i + m' i - a i :=
      by
      conv =>
        lhs
        rw [t.2 h1]
      simp only [Pi.add_apply, coe_tsub, coe_add, Pi.sub_apply]
      rw [Int.ofNat_sub]
      · rw [Int.ofNat_add]
      · rw [add_comm]
        exact monomial_lemma_2 c i
    rw [← add_sub, self_eq_add_right, sub_eq_zero] at t'' 
    symm
    exact t''
  apply le_antisymm
  · exact t.1
  · suffices t' : monomial_degree m ≤ monomial_degree m + monomial_degree m' - monomial_degree a
    · apply t'.trans
      rw [← monomial_degree_add]
      exact monomial_degree_sub_le (m + m') a
    rw [Nat.add_sub_assoc]
    · linarith
    · exact h

private theorem total_degree_p {R σ : Type _} [CommRing R] [IsDomain R] {g : MvPolynomial σ R}
    {m a : σ →₀ ℕ} (hm : DominantMonomial m g) (h_monic : coeff m g = 1) {b : R} (hb : b ≠ 0)
    (ha : a ≠ 0) (h_m_le_a : m ≤ a) :
    totalDegree (monomial a b - monomial (a - m) b * g) < monomialDegree a :=
  by
  apply total_degree_sub_lt
  · by_contra
    simpa [monomial_degree_zero_iff.1 (le_zero_iff.1 (not_lt.1 h))] using ha
  · intro m' hm' h'
    simp only [exists_prop, mem_support_iff, coeff_monomial, ite_eq_right_iff, Ne.def,
      Classical.not_forall] at hm' 
    simp only [← hm'.1, coeff_monomial, if_true, eq_self_iff_true]
    rw [coeff_monomial_mul', if_pos]
    · suffices h : coeff (a - (a - m)) g = 1
      · simp [h]
      suffices h : a - (a - m) = m
      · simp [h, h_monic]
      ext x
      simp only [coe_tsub, Pi.sub_apply, Nat.sub_sub_self (h_m_le_a x)]
    · simp
  · intro m' hm' h
    simp only [mem_support_iff, Ne.def, coeff_monomial_mul'] at hm' 
    rw [coeff_monomial_mul']
    by_cases c : a - m ≤ m'
    · suffices c_m_m' : a = m'
      · simp only [c, if_true, mul_eq_zero, c_m_m'.symm, eq_self_iff_true, coeff_monomial]
        suffices h : coeff (a - (a - m)) g = 1
        · simp [h]
        suffices h : a - (a - m) = m
        · simp [h, h_monic]
        ext x
        simp only [coe_tsub, Pi.sub_apply, Nat.sub_sub_self (h_m_le_a x)]
      simp only [c, if_true, mul_eq_zero, Decidable.not_or_iff_and_not] at hm' 
      have t1 := (dominant_monomial_iff hm) (m' - (a - m)) (mem_support_iff.2 hm'.2)
      apply total_degree_p_aux h_m_le_a h c
      constructor
      · exact t1.1
      · intro h
        symm
        exact t1.2 h
    · simp only [c, eq_self_iff_true, not_true, if_false] at hm' 
      simpa using hm'

private theorem reduce_degree_h_monomial_a_eq_zero {R σ τ : Type _} [CommRing R] [IsDomain R]
    [Fintype τ] {g : τ → MvPolynomial σ R} {m : τ → σ →₀ ℕ}
    (hm : ∀ i : τ, DominantMonomial (m i) (g i)) (h0 : ∀ i : τ, 0 < totalDegree (g i))
    (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) (b : R) : M hm h0 hmonic (monomial 0 b) :=
  by
  use fun i => 0
  constructor
  · intro i
    left
    rfl
  · intro i
    conv in 0 * g _ => rw [MulZeroClass.zero_mul]
    simp only [monomial_zero', sub_zero, Finset.sum_const_zero, IsReduced]
    intro m' hm'
    simp only [exists_prop, coeff_C, mem_support_iff, ite_eq_right_iff, Ne.def,
      Classical.not_forall] at hm' 
    simp only [← hm'.1, nonpos_iff_eq_zero]
    have hmi := (hm i).1
    by_contra
    simp only [max_degree_monomial, h] at hmi 
    simpa [← hmi.2, monomial_degree] using h0 i

private theorem reduce_degree_h_monomial_comp {R σ τ : Type _} [CommRing R] [IsDomain R] [Fintype τ]
    {g h0 : τ → MvPolynomial σ R} {m : σ →₀ ℕ} (a : σ →₀ ℕ) (b : R) (i : τ) :
    monomial a b - ∑ j : τ, (h0 + single i (monomial (a - m) b)) j * g j =
      (monomial a) b - monomial (a - m) b * g i - ∑ j : τ, h0 j * g j :=
  by
  simp only [Pi.add_apply, sub_sub]
  congr
  rw [← sum_univ_single i (monomial (a - m) b * g i), ← Finset.sum_add_distrib]
  congr
  ext1 j
  rw [add_mul, add_comm (h0 j * g j)]
  congr
  by_cases c : i = j
  repeat' simp [c]

private theorem reduce_degree_h_monomial {R σ τ : Type _} [CommRing R] [IsDomain R] [Fintype τ]
    {g : τ → MvPolynomial σ R} {m : τ → σ →₀ ℕ} (hm : ∀ i : τ, DominantMonomial (m i) (g i))
    (h0 : ∀ i : τ, 0 < totalDegree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) (a : σ →₀ ℕ)
    (b : R) (hp : ∀ p : MvPolynomial σ R, p.totalDegree < monomialDegree a → M hm h0 hmonic p) :
    M hm h0 hmonic (monomial a b) :=
  by
  by_cases c : ∀ i, IsReduced (monomial a b) (m i)
  · use fun i => 0
    simp only [true_and_iff, MulZeroClass.zero_mul, imp_true_iff, true_or_iff, eq_self_iff_true,
      sub_zero, Finset.sum_const_zero, c]
  by_cases b_eq_zero : b = 0
  · use fun i => 0
    simp only [IsReduced, b_eq_zero, Finset.not_mem_empty, monomial_zero, MulZeroClass.zero_mul,
      imp_true_iff, true_or_iff, eq_self_iff_true, sub_zero, support_zero, and_self_iff,
      Finset.sum_const_zero]
    sorry
  by_cases a_eq_zero : a = 0
  · rw [a_eq_zero]
    apply reduce_degree_h_monomial_a_eq_zero
  simp only [Classical.not_forall] at c 
  cases' c with i hi
  simp only [IsReduced, Classical.not_forall, exists_prop, Classical.not_not, support_monomial,
    b_eq_zero, if_false, Finset.mem_singleton] at hi 
  cases' hi with a' ha'
  have ha := ha'.2
  rw [ha'.1] at ha 
  clear ha' a'
  let p := monomial a b - monomial (a - m i) b * g i
  have h_total_degree_p : p.total_degree < monomial_degree a :=
    total_degree_p (hm i) (hmonic i) b_eq_zero a_eq_zero ha
  cases' hp p h_total_degree_p with h0 h_h0
  let h := h0 + single i (monomial (a - m i) b)
  use h
  constructor
  · intro j
    by_cases c : j = i
    · right
      rw [c]
      simp only [h, total_degree_monomial_eq_monomial_degree b_eq_zero, single_eq_same,
        Pi.add_apply]
      have t := hm i
      simp only [dominant_monomial, max_degree_monomial] at t 
      rw [← t.1.2]
      clear c j h
      cases' h_h0.1 i with hl hr
      · rw [hl, zero_add]
        apply le_of_eq
        rw [total_degree_monomial_eq_monomial_degree, monomial_degree_sub ha, Nat.sub_add_cancel]
        · exact monomial_degree_le_of_le ha
        · exact b_eq_zero
      · apply
          (add_le_add_right (total_degree_add (h0 i) (monomial (a - m i) b))
              (monomial_degree (m i))).trans
        by_cases c : (h0 i).totalDegree ≤ (monomial (a - m i) b).totalDegree
        · simp only [c, max_eq_right]
          rw [total_degree_monomial_eq_monomial_degree, monomial_degree_sub ha, Nat.sub_add_cancel]
          · exact monomial_degree_le_of_le ha
          · exact b_eq_zero
        · simpa only [(not_le.1 c).le, max_eq_left, t.1.2] using hr.trans h_total_degree_p.le
    · simp only [h, Pi.add_apply, c, true_or_iff, ite_eq_right_iff]
      rw [single_eq_of_ne]
      cases h_h0.1 j
      · left
        simpa using h_1
      · right
        rw [add_zero]
        apply h_1.trans
        rw [total_degree_monomial_eq_monomial_degree]
        · exact le_of_lt h_total_degree_p
        · exact b_eq_zero
      symm
      simpa using c
  · suffices comp : monomial a b - ∑ j : τ, h j * g j = p - ∑ j : τ, h0 j * g j
    · rw [comp]
      exact h_h0.2
    simp only [p, h]
    apply reduce_degree_h_monomial_comp

theorem reduce_degree {R σ τ : Type _} [CommRing R] [IsDomain R] [Fintype τ] (f : MvPolynomial σ R)
    (g : τ → MvPolynomial σ R) {m : τ → σ →₀ ℕ} (hm : ∀ i : τ, DominantMonomial (m i) (g i))
    (h0 : ∀ i : τ, 0 < totalDegree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) :
    ∃ h : τ → MvPolynomial σ R,
      (∀ i : τ, h i = 0 ∨ totalDegree (h i) + totalDegree (g i) ≤ totalDegree f) ∧
        ∀ i : τ, IsReduced (f - ∑ j : τ, h j * g j) (m i) :=
  by
  apply induction_on_new f
  · apply reduce_degree_h_add_weak hm h0 hmonic
  · apply reduce_degree_h_monomial hm h0 hmonic

theorem reduce_degree' {R σ : Type _} [CommRing R] [IsDomain R] [Fintype σ] (f : MvPolynomial σ R)
    (g : σ → MvPolynomial σ R) (hg : ∀ i : σ, g i ∈ supported R ({i} : Set σ))
    (h0 : ∀ i : σ, 0 < totalDegree (g i))
    (hm : ∀ i : σ, coeff (single i (g i).totalDegree) (g i) = 1) :
    ∃ h : σ → MvPolynomial σ R,
      (∀ i : σ, h i = 0 ∨ totalDegree (h i) + totalDegree (g i) ≤ totalDegree f) ∧
        ∀ i : σ, degreeOf i (f - ∑ j : σ, h j * g j) < totalDegree (g i) :=
  by
  have hm' : ∀ i : σ, dominant_monomial (single i (g i).totalDegree) (g i) :=
    by
    intro i
    apply dominant_monomial_single_of_supported_singleton _ (hg i)
    by_contra
    simpa [h] using h0 i
  cases' reduce_degree f g hm' h0 hm with h h_h
  use h
  constructor
  · exact h_h.1
  · intro i
    rw [degree_of_eq_sup, Finset.sup_lt_iff]
    · simpa only [IsReduced, single_le_iff, not_le, Ne.def] using h_h.2 i
    · exact h0 i

theorem reduce_degree_special_case {R σ : Type _} [CommRing R] [IsDomain R] [Fintype σ]
    [DecidableEq σ] (S : σ → Finset R) (hS : ∀ i : σ, 0 < (S i).card) (f : MvPolynomial σ R) :
    ∃ h : σ → MvPolynomial σ R,
      (∀ i : σ, h i = 0 ∨ totalDegree (h i) + (S i).card ≤ totalDegree f) ∧
        ∀ j : σ, degreeOf j (f - ∑ i : σ, h i * ∏ s in S i, (X i - C s)) < (S j).card :=
  by
  let g : σ → MvPolynomial σ R := fun i => ∏ s in S i, (X i - C s)
  let hg : ∀ i : σ, g i ∈ supported R ({i} : Set σ) := fun i => g_S_mem_supported (S i) i
  have h0 : ∀ i : σ, 0 < total_degree (g i) := by
    intro i
    rw [total_degree_g_S]
    exact hS i
  have hm : ∀ i : σ, coeff (single i (g i).totalDegree) (g i) = 1 :=
    by
    intro i
    simpa only [g, total_degree_g_S] using g_S_monic (S i) i
  cases' reduce_degree' f g hg h0 hm with h hh
  use h
  constructor
  · intro i
    rw [← total_degree_g_S (S i) i]
    exact hh.1 i
  · intro i
    rw [← total_degree_g_S (S i) i]
    exact hh.2 i

end MvPolynomial

