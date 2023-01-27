import data.set.image

variables {α β : Type*}

open set

namespace set

@[simp] lemma preimage_mem_singleton_true (s : set α) : (∈ s) ⁻¹' {true} = s := by { ext, simp }
@[simp] lemma preimage_mem_singleton_false (s : set α) : (∈ s) ⁻¹' {false} = sᶜ := by { ext, simp }

@[simp] lemma preimage_symm_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
by simp [symm_diff]

end set

namespace function
variables {f : α → α}

protected lemma involutive.preimage (hf : involutive f) : involutive (preimage f) :=
hf.right_inverse.preimage_preimage

end function
