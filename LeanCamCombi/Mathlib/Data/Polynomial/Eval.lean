import Mathlib.Data.Polynomial.Eval

open scoped BigOperators

namespace Polynomial
variable {ι R : Type*} [Semiring R] {p q r : R[X]}

@[simp] lemma sum_comp (s : Finset ι) (p : ι → R[X]) (q : R[X]) :
    (∑ i in s, p i).comp q = ∑ i in s, (p i).comp q := Polynomial.eval₂_finset_sum _ _ _ _

end Polynomial
