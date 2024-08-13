import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finsupp.Notation

open Finset
open scoped BigOperators

namespace Polynomial
variable {ι R S : Type*} [CommRing R] [CommRing S] [Algebra S R] {w : R →₀ S} {P : R[X]}

/-- Convolve an element of the monoid algebra with a polynomial. Concretely, `w` says how much we
should weigh each translate of the polynomial `P`.  -/
noncomputable def discConv (w : R →₀ S) (P : R[X]) : R[X] :=
  w.sum fun r s ↦ s • P.comp (X + C r)

/-- Discrete forward difference of polynomials. `discForwardDiff P x = P (x + 1) - P x`. -/
noncomputable def discForwardDiff : R[X] → R[X] :=
  discConv ((fun₀ | 1 => 1) - fun₀ | 0 => 1 : R →₀ ℤ)

/-- Discrete backward difference of polynomials. `discBackwardDiff P x = P x - P (x - 1)`. -/
noncomputable def discBackwardDiff : R[X] → R[X] :=
  discConv ((fun₀ | 0 => 1) - fun₀ | -1 => 1 : R →₀ ℤ)

@[simp] lemma discConv_single (r : R) (s : S) :
    discConv (Finsupp.single r s) P = s • P.comp (X + C r) := by simp [discConv]

@[simp] lemma discConv_zero (w : R →₀ S) : discConv w 0 = 0 := by simp [discConv]

lemma discConv_add (w : R →₀ S) (P Q : R[X]) :
    discConv w (P + Q) = discConv w P + discConv w Q := by simp [discConv]

lemma discConv_sub (w : R →₀ S) (P Q : R[X]) :
    discConv w (P - Q) = discConv w P - discConv w Q := by simp [discConv, smul_sub]

@[simp] lemma discConv_neg (w : R →₀ S) (P : R[X]) : discConv w (-P) = -discConv w P := by
  simp [discConv]

lemma discConv_sum (w : R →₀ S) (s : Finset ι) (P : ι → R[X]) :
    discConv w (∑ i in s, P i) = ∑ i in s, discConv w (P i) := by
  simp [discConv, smul_sum, Finsupp.sum]; exact Finset.sum_comm

@[simp] lemma discConv_zero_weight (P : R[X]) : discConv (0 : R →₀ S) P = 0 := by simp [discConv]

lemma discConv_add_weight (v w : R →₀ S) (P : R[X]) :
    discConv (v + w) P = discConv v P + discConv w P :=
  Finsupp.sum_add_index' (by simp) $ by simp [add_smul]

lemma discConv_sub_weight (v w : R →₀ S) (P : R[X]) :
    discConv (v - w) P = discConv v P - discConv w P := Finsupp.sum_sub_index $ by simp [sub_smul]

@[simp] lemma discConv_neg_weight (w : R →₀ S) (P : R[X]) : discConv (-w) P = -discConv w P :=
  (Finsupp.sum_neg_index $ by simp).trans $ by simp [discConv]

@[simp] lemma discConv_sum_weight (s : Finset ι) (w : ι → R →₀ S) (P : R[X]) :
    discConv (∑ i in s, w i) P = ∑ i in s, discConv (w i) P :=
  Finsupp.sum_sum_index' (by simp) $ by simp [add_smul]

@[simp] lemma eval_discConv (w : R →₀ S) (P : R[X]) (x : R) :
    (discConv w P).eval x = w.sum fun r s ↦ s • P.eval (x + r) := by
  simp [discConv, Finsupp.sum,eval_finset_sum]

@[simp] lemma eval_discForwardDiff (P : R[X]) (x : R) :
    (discForwardDiff P).eval x = P.eval (x + 1) - P.eval x := by
  simp_rw [discForwardDiff, discConv_sub_weight, discConv_single]; simp

@[simp] lemma eval_discBackwardDiff (P : R[X]) (x : R) :
    (discBackwardDiff P).eval x = P.eval x - P.eval (x - 1) := by
  simp_rw [discBackwardDiff, discConv_sub_weight, discConv_single]; simp [sub_eq_add_neg]

/-- Associativity of the convolution. Convolving twice a polynomial is the same as convolving once
wt the convolution of the weights. -/
lemma discConv_discConv (v w : AddMonoidAlgebra S R) (P : R[X]) :
    discConv v (discConv w P) = discConv (v * w) P := by
  simp [discConv]
  sorry

lemma coeff_discConv_natDegree (w : R →₀ S) (P : R[X]) :
    coeff (discConv w P) P.natDegree = w.sum (fun _ ↦ id) • leadingCoeff P := by
  sorry -- not so easy but still obvious on paper

variable [Nontrivial S] -- feel free to move this assumption around

private lemma discForwardDiff_aux :
    ((fun₀ | 1 => 1) - fun₀ | 0 => 1 : R →₀ ℤ).sum (fun _ ↦ id) = 0 := by
  classical simp [Finsupp.sum_sub_index, -Finsupp.single_neg]

private lemma discBackwardDiff_aux :
    ((fun₀ | 0 => 1) - fun₀ | -1 => 1 : R →₀ ℤ).sum (fun _ ↦ id) = 0 := by
  classical simp [Finsupp.sum_sub_index, -Finsupp.single_neg]

variable [NoZeroDivisors R] [Nontrivial R] -- and those too

lemma natDegree_discConv_le : natDegree (discConv w P) ≤ natDegree P := by
  refine (natDegree_sum_le _ _).trans $ Finset.sup_le fun r _ ↦ ?_
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
lemma degree_discConv_lt (hw : w.sum (fun _ ↦ id) = 0) (hP : P ≠ 0) :
    degree (discConv w P) < degree P := by
  have := coeff_discConv_natDegree w P
  rw [hw, zero_smul] at this
  -- should be obvious from here
  refine (degree_sum_le _ _).trans_lt $ (Finset.sup_lt_iff ?_).2 ?_
  sorry
  sorry

lemma degree_discForwardDiff_lt (hP : P ≠ 0) :
    degree (discForwardDiff P) < degree P := degree_discConv_lt discForwardDiff_aux hP

lemma degree_discBackwardDiff_lt (hP : P ≠ 0) :
    degree (discBackwardDiff P) < degree P := degree_discConv_lt discBackwardDiff_aux hP

end Polynomial
