import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α]

section Mul
variable [Mul α] {s t : Finset α} {a : α}

@[to_additive]
lemma smul_finset_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image₂_right

attribute [gcongr] div_subset_div_left div_subset_div_right

end Mul
end Finset
