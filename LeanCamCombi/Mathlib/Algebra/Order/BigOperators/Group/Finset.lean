import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Fintype
variable {ι M : Type*} [Fintype ι] [OrderedCancelCommMonoid M] {f g : ι → M}

@[to_additive]
lemma prod_lt_prod (hle : ∀ i, f i ≤ g i) (hlt : ∃ i, f i < g i) : ∏ i, f i < ∏ i, g i := by
  simpa [hle, hlt] using Finset.prod_lt_prod' (s := .univ) (f := f) (g := g)

end Fintype
