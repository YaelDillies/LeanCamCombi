import Mathbin.Data.Set.Image

#align_import mathlib.data.set.image

variable {α β : Type _}

open Set

namespace Set

@[simp]
theorem preimage_mem_singleton_true (s : Set α) : (· ∈ s) ⁻¹' {True} = s := by ext; simp

@[simp]
theorem preimage_mem_singleton_false (s : Set α) : (· ∈ s) ⁻¹' {False} = sᶜ := by ext; simp

#print Set.preimage_symmDiff /-
@[simp]
theorem preimage_symmDiff (f : α → β) (s t : Set β) : f ⁻¹' s ∆ t = (f ⁻¹' s) ∆ (f ⁻¹' t) := by
  simp [symmDiff]
-/

end Set

namespace Function

variable {f : α → α}

protected theorem Involutive.preimage (hf : Involutive f) : Involutive (preimage f) :=
  hf.RightInverse.preimage_preimage

end Function

