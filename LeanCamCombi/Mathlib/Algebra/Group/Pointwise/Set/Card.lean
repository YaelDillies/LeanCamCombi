/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinalities of pointwise operations on sets
-/

open scoped Cardinal Pointwise

namespace Set
variable {G M α : Type*}

section InvolutiveInv
variable [InvolutiveInv G] {s t : Set G}

@[to_additive (attr := simp)]
lemma _root_.Cardinal.mk_inv (s : Set G) : #↥(s⁻¹) = #s := by
  rw [← image_inv, Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

@[to_additive (attr := simp)]
lemma natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s := by
  rw [← image_inv, Nat.card_image_of_injective inv_injective]

end InvolutiveInv

section Group
variable [Group G] [MulAction G α] {s t : Set G}

@[to_additive (attr := simp)]
lemma _root_.Cardinal.mk_smul_set (a : G) (s : Set α) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

@[to_additive (attr := simp)]
lemma natCard_smul_set (a : G) (s : Set α) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective a) _

@[to_additive (attr := deprecated (since := "2024-09-30"))]
alias card_smul_set := Cardinal.mk_smul_set

end Group
end Set
