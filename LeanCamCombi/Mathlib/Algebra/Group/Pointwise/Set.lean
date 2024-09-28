import Mathlib.Algebra.Group.Pointwise.Set

open scoped Pointwise

namespace Set
variable {α β : Type*}

attribute [gcongr] smul_subset_smul vadd_subset_vadd smul_set_mono vadd_set_mono vsub_subset_vsub

section SMul
variable [SMul α β]

@[to_additive]
lemma smul_set_insert (a : α) (b : β) (s : Set β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert_eq ..

end SMul

section DivisionMonoid
variable [DivisionMonoid α] {s t : Set α}

@[to_additive] lemma subset_div_left (ht : 1 ∈ t) : s ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_left _ <| by simpa

@[to_additive] lemma inv_subset_div_right (hs : 1 ∈ s) : t⁻¹ ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

end DivisionMonoid
end Set
