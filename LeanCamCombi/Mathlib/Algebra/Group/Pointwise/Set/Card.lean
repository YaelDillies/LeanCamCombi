import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Data.Set.Card

open scoped Pointwise

namespace Set
variable {G α : Type*} [Group G] [MulAction G α]

@[to_additive (attr := simp)]
lemma encard_smul_set (a : G) (s : Set α) : (a • s).encard = s.encard := by
  simp [encard, PartENat.card]

@[to_additive (attr := simp)]
lemma ncard_smul_set (a : G) (s : Set α) : (a • s).ncard = s.ncard := by simp [ncard]

end Set
