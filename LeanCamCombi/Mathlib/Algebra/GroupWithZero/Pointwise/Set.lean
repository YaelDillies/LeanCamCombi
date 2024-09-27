import Mathlib.Algebra.Group.Pointwise.Finset.NatCard

open scoped Cardinal Pointwise

variable {G α G₀ M₀ : Type*}

namespace Set
section Group
variable [Group G] [MulAction G α]

@[to_additive (attr := simp)]
lemma card_smul_set' (a : G) (s : Set α) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

end Group

section GroupWithZero
variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}

lemma card_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective₀ ha) _

end GroupWithZero
