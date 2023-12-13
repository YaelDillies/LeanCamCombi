/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Tauto

section
variable {ι α : Type*} [LinearOrderedRing α] {f g : ι → α} {s : Set ι} {a b c d : α}

lemma mul_nonneg_iff_pos_imp_nonneg : 0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [←not_le, ←or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

lemma mul_nonneg_iff_neg_imp_nonpos : 0 ≤ a * b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [←neg_mul_neg, mul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_pos_imp_nonpos : a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [←neg_nonneg, ←mul_neg, mul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_neg_imp_nonneg : a * b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [←neg_nonneg, ←neg_mul, mul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end
