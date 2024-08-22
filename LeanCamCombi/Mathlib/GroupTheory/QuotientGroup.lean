import Mathlib.GroupTheory.QuotientGroup.Basic

open Set
open scoped Pointwise

variable {α : Type*}

namespace QuotientGroup
variable [CommGroup α]

@[to_additive]
lemma preimage_image_mk_eq_iUnion_smul (N : Subgroup α) [N.Normal] (s : Set α) :
    (↑) ⁻¹' ((↑) '' s : Set (α ⧸ N)) = ⋃ x : N, x • s := by
  simp_rw [QuotientGroup.preimage_image_mk_eq_iUnion_image N s, ← image_smul, Submonoid.smul_def,
    smul_eq_mul, mul_comm]

end QuotientGroup
