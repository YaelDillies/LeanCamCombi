import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Degree.Lemmas

open Finset
open scoped BigOperators

namespace Polynomial
variable {ι R S : Type*} [CommRing R] [CommRing S] [Algebra S R] {w : R →₀ S} {P : R[X]}

/-- Convolve an element of the monoid algebra with a polynomial. Concretely, `w` says how much we
should weigh each translate of the polynomial `P`.  -/
noncomputable def discConv (w : R →₀ S) (P : R[X]) : R[X] :=
  w.sum λ r s ↦ s • P.comp (X + C r)

/-- Discrete forward difference of polynomials. `discForwardDiff P x = P (x + 1) - P x`. -/
noncomputable def discForwardDiff : R[X] → R[X] := discConv ((fun₀ | 1 => 1) + fun₀ | 0 => -1)

/-- Discrete backward difference of polynomials. `discBackwardDiff P x = P x - P (x - 1)`. -/
noncomputable def discBackwardDiff : R[X] → R[X] := discConv ((fun₀ | 0 => 1) + fun₀ | -1 => -1)

@[simp] lemma discConv_zero (w : R →₀ S) : discConv w 0 = 0 := by simp [discConv]

lemma discConv_add (w : R →₀ S) (P Q : R[X]) :
    discConv w (P + Q) = discConv w P + discConv w Q := by simp [discConv]

lemma discConv_sum (w : R →₀ S) (s : Finset ι) (P : ι → R[X]) :
    discConv w (∑ i in s, P i) = ∑ i in s, discConv w (P i) := sorry -- easy

@[simp] lemma discConv_zero_weight (P : R[X]) : discConv (0 : R →₀ S) P = 0 := by simp [discConv]

lemma discConv_add_weight (v w : R →₀ S) (P : R[X]) :
    discConv (v + w) P = discConv v P + discConv w P :=
  Finsupp.sum_add_index' (by simp) $ by simp [add_smul]

lemma discConv_sum_weight (s : Finset ι) (w : ι → R →₀ S) (P : R[X]) :
    discConv (∑ i in s, w i) P = ∑ i in s, discConv (w i) P := sorry -- easy

@[simp] lemma eval_discConv (w : R →₀ S) (P : R[X]) (x : R) :
    (discConv w P).eval x = w.sum λ r s ↦ s • P.eval (x + r) := by
  simp [discConv, Finsupp.sum,eval_finset_sum]

@[simp] lemma eval_discForwardDiff (P : R[X]) (x : R) :
    (discConv w P).eval x = w.sum λ r s ↦ s • P.eval (x + r) := by
  simp [discConv, Finsupp.sum,eval_finset_sum]

/-- Associativity of the convolution. Convolving twice a polynomial is the same as convolving once
wt the convolution of the weights. -/
lemma discConv_discConv (v w : AddMonoidAlgebra S R) (P : R[X]) :
    discConv v (discConv w P) = discConv (v * w) P := by
  simp [discConv]
  sorry

lemma coeff_discConv_natDegree (w : R →₀ S) (P : R[X]) :
    coeff (discConv w P) P.natDegree = w.sum (λ _ ↦ id) • leadingCoeff P := by
  sorry -- not so easy but still obvious on paper

variable [Nontrivial S]

private lemma discForwardDiff_aux :
    ((fun₀ | 1 => 1) + fun₀ | 0 => -1 : R →₀ S).sum (λ _ ↦ id) = 0 := by
  classical simp [Finsupp.sum_add_index, -Finsupp.single_neg]

private lemma discBackwardDiff_aux :
    ((fun₀ | 0 => 1) + fun₀ | -1 => -1 : R →₀ S).sum (λ _ ↦ id) = 0 := by
  classical simp [Finsupp.sum_add_index, -Finsupp.single_neg]

variable [NoZeroDivisors R] [Nontrivial R]

lemma natDegree_discConv_le : natDegree (discConv w P) ≤ natDegree P := by
  refine' (natDegree_sum_le _ _).trans $ Finset.sup_le λ r _ ↦ _
  dsimp
  simp_rw [algebra_compatible_smul R (w r)]
  refine (natDegree_smul_le _ _).trans ?_
  simp [natDegree_comp]

lemma degree_discConv_le : degree (discConv w P) ≤ degree P := by
  obtain rfl | hP := eq_or_ne P 0
  · simp
  refine degree_le_natDegree.trans $ (Nat.cast_le.2 natDegree_discConv_le).trans ?_
  rw [degree_eq_natDegree hP]

-- easy consequence of `coeff_discConv_natDegree`
lemma degree_discConv_lt (hw : w.sum (λ _ ↦ id) = 0) (hP : P ≠ 0) :
    degree (discConv w P) < degree P := by
  have := coeff_discConv_natDegree w P
  rw [hw, zero_smul] at this
  -- should be obvious from here
  refine' (degree_sum_le _ _).trans_lt $ (Finset.sup_lt_iff _).2 _
  sorry
  sorry

lemma degree_discForwardDiff_lt (hP : P ≠ 0) :
    degree (discForwardDiff P) < degree P := degree_discConv_lt discForwardDiff_aux hP

lemma degree_discBackwardDiff_lt (hP : P ≠ 0) :
    degree (discBackwardDiff P) < degree P := degree_discConv_lt discBackwardDiff_aux hP

end Polynomial
