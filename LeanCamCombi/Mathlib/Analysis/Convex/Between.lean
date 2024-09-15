import Mathlib.Analysis.Convex.Between
import LeanCamCombi.Mathlib.LinearAlgebra.AffineSpace.AffineMap

open AffineMap

variable {k V P : Type*}

section OrderedRing
variable [OrderedRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P}
  {p₀ p₁ p₂ : P}

lemma AffineSubspace.mem_of_wbtw (h₀₁₂ : Wbtw k p₀ p₁ p₂) (h₀ : p₀ ∈ Q) (h₂ : p₂ ∈ Q) : p₁ ∈ Q := by
  obtain ⟨ε, -, rfl⟩ := h₀₁₂; exact lineMap_mem _ h₀ h₂

end OrderedRing

section LinearOrderedField
variable [LinearOrderedField k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  {Q : AffineSubspace k P} {p₀ p₁ p₂ : P}

lemma AffineSubspace.right_mem_of_wbtw (h₀₁₂ : Wbtw k p₀ p₁ p₂) (h₀ : p₀ ∈ Q) (h₁ : p₁ ∈ Q)
    (h₀₁ : p₀ ≠ p₁) : p₂ ∈ Q := by
  obtain ⟨ε, -, rfl⟩ := h₀₁₂
  have hε : ε ≠ 0 := by rintro rfl; simp at h₀₁
  simpa [hε] using lineMap_mem ε⁻¹ h₀ h₁

end LinearOrderedField
