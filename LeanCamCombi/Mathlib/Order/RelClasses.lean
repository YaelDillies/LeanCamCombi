import Mathlib.Order.RelClasses

variable {α : Type*} [Preorder α]

lemma wellFounded_lt [WellFoundedLT α] : @WellFounded α (· < ·) := IsWellFounded.wf
lemma wellFounded_gt [WellFoundedGT α] : @WellFounded α (· > ·) := IsWellFounded.wf
