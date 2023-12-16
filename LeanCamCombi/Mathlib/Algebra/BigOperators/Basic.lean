import Mathlib.Algebra.BigOperators.Basic

open scoped BigOperators

namespace Finset
variable {ι M : Type*} [CommMonoid M] [DecidableEq ι]

@[to_additive]
lemma prod_mulIndicator_eq_prod_inter (s t : Finset ι) (f : ι → M) :
    ∏ i in s, (t : Set ι).mulIndicator f i = ∏ i in s ∩ t, f i := by
  rw [←filter_mem_eq_inter, prod_mulIndicator_eq_prod_filter]; rfl

end Finset
