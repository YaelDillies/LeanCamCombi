import Mathlib.SetTheory.Cardinal.Finite

open Cardinal Function

namespace Nat
variable {α : Type*}
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
