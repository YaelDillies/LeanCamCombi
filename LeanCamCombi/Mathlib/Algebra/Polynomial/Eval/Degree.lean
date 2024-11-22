import Mathlib.Algebra.Polynomial.Eval.Degree
import LeanCamCombi.Mathlib.Algebra.Polynomial.Degree.Operations

variable {R S : Type*} [CommRing R] [CommRing S]

namespace Polynomial
variable {f : R →+* S} {p : R[X]}

lemma degree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : p ≠ 0) : (p.map f).degree < p.degree := by
  refine (degree_map_le _ _).lt_of_ne fun hpq ↦ hp₀ ?_
  rw [leadingCoeff, ← coeff_map, ← natDegree_eq_natDegree hpq, ← leadingCoeff, leadingCoeff_eq_zero]
    at hp
  rw [← degree_eq_bot, ← hpq, hp, degree_zero]

-- TODO: There is a version of this where we assume `p` nonconstant instead of `map f p ≠ 0`
lemma natDegree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : map f p ≠ 0) :
    (p.map f).natDegree < p.natDegree :=
  natDegree_lt_natDegree' hp₀ <| degree_map_lt hp <| by rintro rfl; simp at hp₀

end Polynomial
