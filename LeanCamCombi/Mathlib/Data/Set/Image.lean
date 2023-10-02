import Mathlib.Data.Set.Image

variable {α β : Type*}

namespace Set

@[simp] lemma preimage_mem_singleton_true (s : Set α) : (· ∈ s) ⁻¹' {True} = s := by ext; simp
@[simp] lemma preimage_mem_singleton_false (s : Set α) : (· ∈ s) ⁻¹' {False} = sᶜ := by ext; simp

end Set
