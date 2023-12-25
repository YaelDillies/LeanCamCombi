import SetTheory.Cardinal.Basic

#align_import mathlib.set_theory.cardinal.basic

open Function Set Order

open scoped BigOperators Cardinal Classical

namespace Cardinal

variable {α : Type _} {c : Cardinal}

#print Cardinal.toNat_eq_zero /-
@[simp]
theorem toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c :=
  by
  simp only [toNat, ZeroHom.coe_mk, dite_eq_right_iff, Classical.or_iff_not_imp_right, not_le]
  refine' forall_congr' fun h => _
  rw [← @Nat.cast_eq_zero Cardinal, ← Classical.choose_spec (to_nat._proof_1 _ h)]
-/

#print Cardinal.toNat_ne_zero /-
theorem toNat_ne_zero : toNat c ≠ 0 ↔ c ≠ 0 ∧ c < ℵ₀ := by simp [not_or]
-/

#print Cardinal.toNat_pos /-
@[simp]
theorem toNat_pos : 0 < toNat c ↔ c ≠ 0 ∧ c < ℵ₀ :=
  pos_iff_ne_zero.trans toNat_ne_zero
-/

#print Cardinal.aleph0_le_mk_iff /-
theorem aleph0_le_mk_iff : aleph0 ≤ mk α ↔ Infinite α :=
  infinite_iff.symm
-/

#print Cardinal.mk_lt_aleph0_iff /-
theorem mk_lt_aleph0_iff : mk α < aleph0 ↔ Finite α := by simp [← not_le, aleph_0_le_mk_iff]
-/

end Cardinal

