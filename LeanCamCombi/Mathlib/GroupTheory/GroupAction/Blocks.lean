import Mathlib.GroupTheory.GroupAction.Blocks

open Set
open scoped Pointwise

namespace MulAction
variable {G X : Type*}

section SMul
variable [SMul G X] {B : Set X} {s : Set G} {a b : G}

@[to_additive]
lemma IsBlock.eq_of_subset (hB : IsBlock G B) (hab : a • B ⊆ b • B) : a • B = b • B := by
  by_contra! hab'
  obtain rfl : B = ∅ := by simpa using (hB hab').eq_bot_of_le hab
  simp at hab'

@[to_additive]
lemma IsBlock.not_smul_set_ssubset_smul_set (hB : IsBlock G B) : ¬ a • B ⊂ b • B :=
  fun hab ↦ hab.ne <| hB.eq_of_subset hab.subset

@[to_additive]
lemma IsBlock.disjoint_smul_set_smul (hB : IsBlock G B) (has : ¬ a • B ⊆ s • B) :
    Disjoint (a • B) (s • B) := by
  rw [← iUnion_smul_set, disjoint_iUnion₂_right]
  exact fun b hb ↦ hB fun h ↦ has <| h.trans_subset <| smul_set_subset_smul hb

@[to_additive]
lemma IsBlock.disjoint_smul_smul_set (hB : IsBlock G B) (has : ¬ a • B ⊆ s • B) :
    Disjoint (s • B) (a • B) := (hB.disjoint_smul_set_smul has).symm

end SMul

section MulAction
variable [Monoid G] [MulAction G X] {B : Set X} {s : Set G}

@[to_additive]
lemma IsBlock.disjoint_smul_right (hB : IsBlock G B) (hs : ¬ B ⊆ s • B) : Disjoint B (s • B) := by
  simpa using hB.disjoint_smul_set_smul (a := 1) (by simpa using hs)

@[to_additive]
lemma IsBlock.disjoint_smul_left (hB : IsBlock G B) (hs : ¬ B ⊆ s • B) : Disjoint (s • B) B :=
  (hB.disjoint_smul_right hs).symm

end MulAction
