/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.Cardinal.Finite

/-!
# For mathlib

A few things to move. If they are here, it's because they have no obvious home in mathlib.
-/

open scoped Pointwise

namespace Subgroup
variable {α : Type*} [Group α] {s : Subgroup α} {a : α}

@[norm_cast, to_additive]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = ⊥ := (SetLike.ext'_iff.trans (by rfl)).symm

@[to_additive]
lemma smul_coe (ha : a ∈ s) : a • (s : Set α) = s := by
  ext; rw [Set.mem_smul_set_iff_inv_smul_mem]; exact Subgroup.mul_mem_cancel_left _ (inv_mem ha)

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

namespace Subgroup
variable {α β : Type*} [Group α] [Group β] [MulAction α β] [IsScalarTower α β β]

open Set

@[to_additive]
lemma pairwiseDisjoint_smul (s : Subgroup β) :
    (Set.range fun a : α ↦ a • (s : Set β)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  simp only [Function.onFun, id_eq, disjoint_left] at hab ⊢
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe hc, ← smul_assoc, ← hcd, smul_assoc, smul_coe hc, smul_coe hd]

end Subgroup

namespace CharP
-- variable {R : Type*} [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b n : ℕ}

-- lemma addOrderOf_cast (hn : n ≠ 0) : addOrderOf (n : R) = p / p.gcd n := sorry
end CharP

