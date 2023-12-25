/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import Nullstellensatz.Homogenization

#align_import nullstellensatz.degree

/-!
# Total_degree, etc
-/


open Set Function Finsupp AddMonoidAlgebra

open scoped BigOperators

universe u v

variable {α : Type v}

namespace MvPolynomial

variable {R : Type _} {σ : Type _}

attribute [local instance] Classical.propDecidable

theorem x_ne_zero [CommSemiring R] [Nontrivial R] (j : σ) : (X j : MvPolynomial σ R) ≠ 0 :=
  ne_zero_iff.2 ⟨single j 1, by simp⟩

theorem totalDegree_sum [CommSemiring R] (s : Finset α) (p : α → MvPolynomial σ R) :
    totalDegree (∑ i : α in s, p i) ≤ s.sup fun i => totalDegree (p i) :=
  by
  apply Finset.cons_induction_on s
  simp
  clear s
  intro a s h_a_in_s h_ind
  repeat' rw [Finset.sum_cons]
  apply (total_degree_add _ _).trans
  simp [h_ind]

theorem totalDegree_hMul_x_le [CommSemiring R] [Nontrivial R] (f : MvPolynomial σ R) (j : σ) :
    totalDegree (f * X j) ≤ totalDegree f + 1 :=
  by
  apply (total_degree_mul f (X j)).trans
  simp only [total_degree_X]

-- The following depends on https://github.com/leanprover-community/flt-regular
-- this appears in flt-regular as support_add_eq
theorem support_add_disjoint [CommSemiring R] {f g : MvPolynomial σ R}
    (h : Disjoint f.support g.support) : (f + g).support = f.support ∪ g.support :=
  Finsupp.support_add_eq h

theorem totalDegree_add_eq_of_disjoint_support [CommSemiring R] {f g : MvPolynomial σ R}
    (h : Disjoint f.support g.support) : totalDegree (f + g) = max f.totalDegree g.totalDegree :=
  by
  simp only [total_degree, support_add_disjoint h]
  apply Finset.sup_union

theorem totalDegree_add_monomial [CommSemiring R] (f : MvPolynomial σ R) (a : σ →₀ ℕ) (b : R)
    (h : a ∉ f.support) (h_b : b ≠ 0) :
    totalDegree (monomial a b + f) = LinearOrder.max (totalDegree (monomial a b)) (totalDegree f) :=
  by
  apply total_degree_add_eq_of_disjoint_support
  simp [support_monomial, h_b, h]

open scoped Pointwise

-- this uses code from flt-regular
theorem support_mul1 [CommSemiring R] [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p * q).support ⊆ p.support + q.support := by convert support_mul' p q

theorem support_mul'' [CommRing R] {f g : MvPolynomial σ R} {m : σ →₀ ℕ} (h : m ∈ (f * g).support) :
    ∃ mf mg, mf ∈ f.support ∧ mg ∈ g.support ∧ mf + mg = m :=
  Finset.mem_add.1 <| support_mul1 f g h

-- this uses code from flt-regular
theorem totalDegree_mul' [CommRing R] [IsDomain R] {f g : MvPolynomial σ R} (hf : f ≠ 0)
    (hg : g ≠ 0) : totalDegree (f * g) = totalDegree f + totalDegree g :=
  totalDegree_hMul_eq hf hg

theorem totalDegree_hMul_x [CommRing R] [IsDomain R] {f : MvPolynomial σ R} (h : f ≠ 0) (j : σ) :
    totalDegree (f * X j) = totalDegree f + 1 := by simp [total_degree_mul' h (X_ne_zero j)]

end MvPolynomial

