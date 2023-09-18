import Mathlib.Data.Fintype.Powerset

namespace Finset
variable {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α} {n : ℕ}

lemma filter_subset_univ (s : Finset α) : filter (fun t ↦ t ⊆ s) univ = powerset s := by
  ext; simp

lemma mem_powersetLen_univ : s ∈ powersetLen n univ ↔ s.card = n := by simp

end Finset
