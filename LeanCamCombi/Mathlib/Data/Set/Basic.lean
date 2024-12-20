import Mathlib.Data.Set.Basic

namespace Set
variable {α : Type*} {s : Set α} {a : α}

lemma diff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := by
  ext; simp [and_right_comm]

end Set
