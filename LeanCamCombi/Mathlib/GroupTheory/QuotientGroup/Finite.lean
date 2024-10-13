import Mathlib.GroupTheory.QuotientGroup.Finite
import LeanCamCombi.Mathlib.Algebra.Group.Subgroup.Pointwise

open scoped Pointwise

namespace Subgroup
variable {α : Type*} [Group α] {s : Subgroup α} {a : α}

-- to be simplified
@[to_additive]
lemma subgroup_mul_card_eq_mul (s : Subgroup α) (t : Set α) :
    Nat.card s * Nat.card (t.image (↑) : Set (α ⧸ s)) = Nat.card (t * (s : Set α)) := by
  rw [← Nat.card_prod, Nat.card_congr]
  apply Equiv.trans (QuotientGroup.preimageMkEquivSubgroupProdSet _ _).symm
  rw [QuotientGroup.preimage_image_mk]
  apply Set.BijOn.equiv id
  convert Set.bijOn_id _
  ext x
  constructor
  · simp only [Set.mem_iUnion, Set.mem_preimage, Subtype.exists, exists_prop, Set.mem_mul]
    aesop
  · simp only [Set.mem_iUnion, Set.mem_preimage, Subtype.exists, exists_prop, forall_exists_index,
    and_imp]
    intro y hys hxy
    rw [← mul_inv_cancel_right x y]
    apply Set.mul_mem_mul hxy (by simpa)

end Subgroup
