import SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Basic

#align_import mathlib.set_theory.cardinal.finite

open Cardinal

namespace Nat

variable {α : Type _}

#print Nat.card_eq_zero /-
@[simp]
theorem card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  simp [Nat.card, mk_eq_zero_iff, aleph_0_le_mk_iff]
-/

#print Nat.card_ne_zero /-
theorem card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by simp [not_or]
-/

#print Nat.card_pos_iff /-
theorem card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph_0_iff]
-/

#print Nat.card_pos /-
@[simp]
theorem card_pos [Nonempty α] [Finite α] : 0 < Nat.card α :=
  card_pos_iff.2 ⟨‹_›, ‹_›⟩
-/

#print Nat.card_mono /-
-- TODO: Golf proof
-- lemma finite_of_card_ne_zero (h : nat.card α ≠ 0) : finite α := (card_ne_zero.1 h).2
theorem card_mono {s t : Set α} (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t :=
  toNat_le_of_le_of_lt_aleph0 ht.lt_aleph0 <| mk_le_mk_of_subset h
-/

end Nat

namespace Set

variable {α : Type _} {s : Set α}

#print Set.Infinite.card_eq_zero /-
theorem Infinite.card_eq_zero (hs : s.Infinite) : Nat.card s = 0 :=
  @Nat.card_eq_zero_of_infinite _ hs.to_subtype
-/

end Set

