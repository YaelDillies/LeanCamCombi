import Mathlib.Algebra.Polynomial.Degree.Operations

namespace Polynomial
variable {R S : Type*} [Semiring R] [Semiring S]

-- TODO: Replace `natDegree_lt_natDegree`
lemma natDegree_lt_natDegree' {p : R[X]} {q : S[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by
  by_cases hq : q = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq

lemma natDegree_eq_natDegree {p : R[X]} {q : S[X]} (hpq : p.degree = q.degree) :
    p.natDegree = q.natDegree := by simp [natDegree, hpq]

end Polynomial
