import Mathlib.Algebra.MvPolynomial.CommRing

namespace MvPolynomial

lemma degrees_sub_le {σ R} [CommRing R] [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p - q).degrees ≤ p.degrees ∪ q.degrees := by
  simp_rw [degrees_def]; exact AddMonoidAlgebra.supDegree_sub_le
