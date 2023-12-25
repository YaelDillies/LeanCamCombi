import Mathlib.Algebra.IndicatorFunction

#align_import mathlib.algebra.indicator_function

open scoped BigOperators

namespace Finset

variable {α ι M : Type _} [CommMonoid M] [DecidableEq ι]

@[to_additive]
theorem prod_inter_eq_prod_mulIndicator (s t : Finset ι) (f : ι → M) :
    ∏ i in s ∩ t, f i = ∏ i in s, (t : Set ι).mulIndicator f i := by
  simp [prod_mul_indicator_eq_prod_filter, filter_mem_eq_inter]

end Finset
