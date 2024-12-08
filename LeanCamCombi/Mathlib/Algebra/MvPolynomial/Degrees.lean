import Mathlib.Algebra.MvPolynomial.Degrees
import LeanCamCombi.Mathlib.Algebra.Algebra.Operations

namespace MvPolynomial
variable {R σ : Type*} [CommSemiring R] {m n : Multiset σ} {p : MvPolynomial σ R}

variable (R σ n) in
def degreesLE : Submodule R (MvPolynomial σ R) where
  carrier := {p | p.degrees ≤ n}
  add_mem' {a b} ha hb := by classical exact (MvPolynomial.degrees_add a b).trans (sup_le ha hb)
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    dsimp
    rw [Algebra.smul_def]
    refine (MvPolynomial.degrees_mul _ _).trans ?_
    simpa [MvPolynomial.degrees_C] using hx

@[simp] lemma mem_degreesLE : p ∈ degreesLE R σ n ↔ p.degrees ≤ n := Iff.rfl

lemma degreesLE_mul : degreesLE R σ m * degreesLE R σ n = degreesLE R σ (m + n) := by
  classical
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro x hx y hy
    exact (degrees_mul _ _).trans (add_le_add hx hy)
  · intro x hx
    rw [x.as_sum]
    refine sum_mem fun i hi ↦ ?_
    replace hi : i.toMultiset ≤ m + n := (Finset.le_sup hi).trans hx
    let a := (i.toMultiset - n).toFinsupp
    let b := (i.toMultiset ⊓ n).toFinsupp
    have : a + b = i := Multiset.toFinsupp.symm.injective (by simp [a, b, Multiset.sub_add_inter])
    have ha : a.toMultiset ≤ m := by simpa [a, add_comm (a := n)] using hi
    have hb : b.toMultiset ≤ n := by simp [b, Multiset.inter_le_right]
    have : monomial i (x.coeff i) = monomial a (x.coeff i) * monomial b 1 := by
      simp [this]
    rw [this]
    exact Submodule.mul_mem_mul ((degrees_monomial _ _).trans ha) ((degrees_monomial _ _).trans hb)

@[simp]
lemma degreesLE_zero {R σ : Type*} [CommSemiring R] :
    degreesLE R σ 0 = 1 := by
  apply le_antisymm
  · intro x hx
    simp only [mem_degreesLE, nonpos_iff_eq_zero] at hx
    have := (totalDegree_eq_zero_iff_eq_C (p := x)).mp
      (Nat.eq_zero_of_le_zero (x.totalDegree_le_degrees_card.trans (by simp [hx])))
    exact ⟨x.coeff 0, by simp [Algebra.smul_def, ← this]⟩
  · simp

variable (R σ n) (k : ℕ) in
lemma degreesLE_pow : ∀ k : ℕ, degreesLE R σ n ^ k = degreesLE R σ (k • n)
  | 0 => by simp
  | k + 1 => by simp only [pow_succ, degreesLE_pow k, degreesLE_mul, add_smul, one_smul]
