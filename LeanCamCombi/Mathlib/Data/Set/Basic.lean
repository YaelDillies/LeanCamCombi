import Mathlib.Data.Set.Basic

namespace Set
variable {α : Type*} {s : Set α} {a : α}

lemma sdiff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := by
  ext; simp [and_right_comm]

lemma inter_sdiff_left_comm (s t u : Set α) : s ∩ (t \ u) = t ∩ (s \ u) := by
  simp_rw [← inter_diff_assoc, inter_comm]

end Set
