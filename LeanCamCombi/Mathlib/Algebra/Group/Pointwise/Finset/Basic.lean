import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α] [Mul α] {s t : Finset α} {a : α}

lemma smul_finset_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image₂_right

end Finset
