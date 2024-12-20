import Mathlib.Data.Set.Basic

namespace Set
variable {α : Type*} {s : Set α} {a : α}

lemma diff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := by
  ext; simp [and_right_comm]

lemma insert_diff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by aesop

lemma insert_erase_invOn :
    InvOn (insert a) (fun s ↦ s \ {a}) {s : Set α | a ∈ s} {s : Set α | a ∉ s} :=
  ⟨fun _s ha ↦ insert_diff_self_of_mem ha, fun _s ↦ insert_diff_self_of_not_mem⟩

@[gcongr] protected alias ⟨_, GCongr.singleton_subset_singleton⟩ := singleton_subset_singleton

end Set
