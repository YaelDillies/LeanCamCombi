import Mathlib.Algebra.IndicatorFunction

open scoped BigOperators

namespace Finset
variable {ι M : Type*} [CommMonoid M] [DecidableEq ι]

@[to_additive]
lemma prod_inter_eq_prod_mulIndicator (s t : Finset ι) (f : ι → M) :
    ∏ i in s ∩ t, f i = ∏ i in s, (t : Set ι).mulIndicator f i := by
  rw [←filter_mem_eq_inter, prod_mulIndicator_eq_prod_filter]; rfl

end Finset
