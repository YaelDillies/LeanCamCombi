import Mathlib.Algebra.Group.Subgroup.Pointwise

open Set
open scoped Pointwise

namespace Subgroup
variable {α β : Type*} [Group α] {s : Subgroup α} {a : α}

@[norm_cast, to_additive]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = ⊥ := (SetLike.ext'_iff.trans (by rfl)).symm

@[to_additive]
lemma smul_coe (ha : a ∈ s) : a • (s : Set α) = s := by
  ext; rw [Set.mem_smul_set_iff_inv_smul_mem]; exact Subgroup.mul_mem_cancel_left _ (inv_mem ha)

variable [Group β] [MulAction α β] [IsScalarTower α β β]

@[to_additive]
lemma pairwiseDisjoint_smul (s : Subgroup β) :
    (Set.range fun a : α ↦ a • (s : Set β)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  simp only [Function.onFun, id_eq, disjoint_left] at hab ⊢
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe hc, ← smul_assoc, ← hcd, smul_assoc, smul_coe hc, smul_coe hd]

end Subgroup
