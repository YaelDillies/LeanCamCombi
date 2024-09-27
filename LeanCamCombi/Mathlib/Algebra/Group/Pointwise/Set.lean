import Mathlib.Algebra.Group.Pointwise.Set

open scoped Pointwise

namespace Set
variable {α β : Type*} [SMul α β]

attribute [gcongr] smul_subset_smul vadd_subset_vadd smul_set_mono vadd_set_mono

@[to_additive]
lemma smul_set_insert (a : α) (b : β) (s : Set β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert_eq ..

end Set
