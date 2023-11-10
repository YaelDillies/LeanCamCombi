import Mathlib.Control.ULift
import Mathlib.SetTheory.Cardinal.Finite
import LeanCamCombi.Mathlib.SetTheory.Cardinal.Basic

open Cardinal Function

universe u v u' v'

namespace ULift
variable {α : Type u} {β : Type v} {f : α → β}

protected def map' (f : α → β) (a : ULift.{u'} α) : ULift.{v'} β := ULift.up.{v'} (f a.down)

lemma map_injective (hf : Injective f) :
    Injective (ULift.map' f : ULift.{u'} α → ULift.{v'} β) :=
  up_injective.comp <| hf.comp down_injective

lemma map_surjective (hf : Surjective f) :
    Surjective (ULift.map' f : ULift.{u'} α → ULift.{v'} β) :=
  up_surjective.comp <| hf.comp down_surjective

end ULift

namespace Nat
variable {α : Type*}

@[simp]
lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  simp [Nat.card, mk_eq_zero_iff, aleph0_le_mk_iff]

lemma card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by simp [not_or]

lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff]

@[simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩

lemma card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α → β)
    (hf : Injective f) : Nat.card α ≤ Nat.card β := by
  simpa using toNat_le_of_le_of_lt_aleph0 (by simp [lt_aleph0_of_finite]) $
    mk_le_of_injective (α := ULift.{max u v} α) (β := ULift.{max u v} β) $ ULift.map_injective hf

lemma card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α → β)
    (hf : Surjective f) : Nat.card β ≤ Nat.card α := by
  simpa using toNat_le_of_le_of_lt_aleph0 (by simp [lt_aleph0_of_finite]) $
    mk_le_of_surjective (α := ULift.{max u v} α) (β := ULift.{max u v} β) $ ULift.map_surjective hf

-- TODO: Golf proof
-- lemma finite_of_card_ne_zero (h : nat.card α ≠ 0) : finite α := (card_ne_zero.1 h).2
lemma card_mono {s t : Set α} (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t :=
  toNat_le_of_le_of_lt_aleph0 ht.lt_aleph0 <| mk_le_mk_of_subset h

end Nat

namespace Set
variable {α : Type*} {s : Set α}

lemma Infinite.card_eq_zero (hs : s.Infinite) : Nat.card s = 0 :=
  @Nat.card_eq_zero_of_infinite _ hs.to_subtype

end Set
