import Mathlib.Logic.Nontrivial.Basic

variable {α : Type*}

lemma not_subsingleton_iff_nontrivial : ¬ Subsingleton α ↔ Nontrivial α := by
  rw [←not_nontrivial_iff_subsingleton, not_not]
