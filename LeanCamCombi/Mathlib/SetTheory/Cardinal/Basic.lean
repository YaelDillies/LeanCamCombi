import Mathlib.SetTheory.Cardinal.Basic

open Function Set Order
open scoped BigOperators Cardinal Classical

namespace Cardinal
variable {α : Type*} {c : Cardinal}

@[simp]
lemma toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c := by
  simp only [toNat, ZeroHom.coe_mk, dite_eq_right_iff, or_iff_not_imp_right, not_le]
  refine' forall_congr' fun h => _
  rw [←@Nat.cast_eq_zero Cardinal, ← Classical.choose_spec (p := fun n : ℕ ↦ c = n)]

lemma toNat_ne_zero : toNat c ≠ 0 ↔ c ≠ 0 ∧ c < ℵ₀ := by simp [not_or]

@[simp] lemma toNat_pos : 0 < toNat c ↔ c ≠ 0 ∧ c < ℵ₀ := pos_iff_ne_zero.trans toNat_ne_zero

lemma aleph0_le_mk_iff : aleph0 ≤ mk α ↔ Infinite α := infinite_iff.symm
lemma mk_lt_aleph0_iff : mk α < aleph0 ↔ Finite α := by simp [← not_le, aleph0_le_mk_iff]

end Cardinal
