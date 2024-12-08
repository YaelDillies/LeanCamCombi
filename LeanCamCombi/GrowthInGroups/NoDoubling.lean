/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.GroupTheory.GroupAction.Defs
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Sets with no doubling

This file characterises sets with no doubling (finsets `A` such that `#(A ^ 2) = #A`) as the sets
which are either empty or translates of a subgroup.
-/

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {A : Finset G}

/-- A set with no doubling is either empty or the translate of a subgroup. -/
@[to_additive "A set with no doubling is either empty or the translate of a subgroup."]
lemma exists_subgroup_of_no_doubling (hA : #(A * A) ≤ #A) :
    ∃ H : Subgroup G, ∀ a ∈ A, a •> (H : Set G) = A ∧ (H : Set G) <• a = A := by
  have smul_A {a} (ha : a ∈ A) : a •> A = A * A :=
    eq_of_subset_of_card_le (smul_finset_subset_mul ha) (by simpa)
  have op_smul_A {a} (ha : a ∈ A) : A <• a = A * A :=
    eq_of_subset_of_card_le (op_smul_finset_subset_mul ha) (by simpa)
  have smul_A_eq_op_smul_A {a} (ha : a ∈ A) : a •> A = A <• a := by rw [smul_A ha, op_smul_A ha]
  have smul_A_eq_op_smul_A' {a} (ha : a ∈ A) : a⁻¹ •> A = A <• a⁻¹ := by
    rw [inv_smul_eq_iff, smul_comm, smul_A_eq_op_smul_A ha, op_inv, inv_smul_smul]
  let H := stabilizer G A
  have inv_smul_A {a} (ha : a ∈ A) : a⁻¹ • (A : Set G) = H := by
    ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨b, hb, rfl⟩
      simp [H, mul_smul, inv_smul_eq_iff, smul_A ha, smul_A hb]
    · norm_cast
      rwa [smul_A_eq_op_smul_A' ha, op_inv, mem_inv_smul_finset_iff, op_smul_eq_mul, ← smul_eq_mul,
        ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨H, fun a ha ↦ ⟨?_, ?_⟩⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_op_smul_A ha, inv_smul_smul]

end Finset
