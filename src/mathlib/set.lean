import data.set.image

variables {α β : Type*}

namespace set

@[simp] lemma preimage_mem_singleton_true (s : set α) : (∈ s) ⁻¹' {true} = s := by { ext, simp }
@[simp] lemma preimage_mem_singleton_false (s : set α) : (∈ s) ⁻¹' {false} = sᶜ := by { ext, simp }

@[simp] lemma preimage_symm_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
by simp [symm_diff]

end set
