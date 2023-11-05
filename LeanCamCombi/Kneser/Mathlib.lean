/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Finset.Pointwise
import Mathlib.GroupTheory.Subgroup.Basic
import LeanCamCombi.Mathlib.SetTheory.Cardinal.Finite

/-!
# For mathlib

A few things to move. If they are here, it's because they have no obvious home in mathlib.
-/

open scoped Pointwise

namespace Nat
variable {α β : Type*} [Group α] [MulAction α β]

open Cardinal

@[to_additive (attr := simp)]
lemma card_smul_set (a : α) (s : Set β) : Nat.card (a • s) = Nat.card s := by
  obtain hs | hs := s.infinite_or_finite
  · rw [hs.card_eq_zero, hs.smul_set.card_eq_zero]
  classical
  lift s to Finset β using hs
  rw [← Finset.coe_smul_finset]
  simp [-Finset.coe_smul_finset]

end Nat

namespace Subgroup
variable {α : Type*} [Group α] {s : Subgroup α} {a : α}

@[norm_cast, to_additive]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = ⊥ := (SetLike.ext'_iff.trans (by rfl)).symm

@[to_additive]
lemma smul_coe (ha : a ∈ s) : a • (s : Set α) = s := by
  ext; rw [Set.mem_smul_set_iff_inv_smul_mem]; exact Subgroup.mul_mem_cancel_left _ (inv_mem ha)

end Subgroup

namespace Subgroup
variable {α β : Type*} [Group α] [Group β] [MulAction α β] [IsScalarTower α β β]

open Set

@[to_additive]
lemma pairwiseDisjoint_smul (s : Subgroup β) :
    (Set.range fun a : α => a • (s : Set β)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  simp only [Function.onFun, id_eq, disjoint_left] at hab ⊢
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine' hab _
  rw [← smul_coe hc, ← smul_assoc, ← hcd, smul_assoc, smul_coe hc, smul_coe hd]

end Subgroup

namespace CharP
variable {R : Type*} [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b n : ℕ}

-- lemma add_order_of_cast (hn : n ≠ 0) : add_order_of (n : R) = p / p.gcd n := sorry
end CharP
