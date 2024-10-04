import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Finsupp.Order

namespace Finsupp
variable {ι κ α β : Type*}

section Preorder
variable [Zero α] [Preorder α] {i : ι} {a b : α}

@[simp] lemma single_le_single : single i a ≤ single i b ↔ a ≤ b := by
  classical exact Pi.single_le_single

lemma single_mono : Monotone (single i : α → ι →₀ α) := fun _ _ ↦ single_le_single.2

@[gcongr] alias ⟨_, GCongr.single_mono⟩ := single_le_single

@[simp] lemma single_nonneg : 0 ≤ single i a ↔ 0 ≤ a := by classical exact Pi.single_nonneg
@[simp] lemma single_nonpos : single i a ≤ 0 ↔ a ≤ 0 := by classical exact Pi.single_nonpos

variable [OrderedAddCommMonoid β]

lemma sum_le_sum_index [DecidableEq ι] {f₁ f₂ : ι →₀ α} {h : ι → α → β} (hf : f₁ ≤ f₂)
    (hh : ∀ i ∈ f₁.support ∪ f₂.support, Monotone (h i))
    (hh₀ : ∀ i ∈ f₁.support ∪ f₂.support, h i 0 = 0): f₁.sum h ≤ f₂.sum h := by
  classical
  rw [sum_of_support_subset _ Finset.subset_union_left _ hh₀,
    sum_of_support_subset _ Finset.subset_union_right _ hh₀]
  exact Finset.sum_le_sum fun i hi ↦ hh _ hi $ hf _

end Preorder

section OrderedAddCommMonoid
variable [Zero α] [OrderedAddCommMonoid β]

lemma sum_le_sum {f : ι →₀ α} {h₁ h₂ : ι → α → β} (h : ∀ i ∈ f.support, h₁ i (f i) ≤ h₂ i (f i)) :
    f.sum h₁ ≤ f.sum h₂ := Finset.sum_le_sum h

end OrderedAddCommMonoid

variable [OrderedAddCommMonoid α] {i : ι} {a b : α} {f₁ f₂ g : ι →₀ α}

lemma mapDomain_mono {f : ι → κ} : Monotone (mapDomain f : (ι →₀ α) → (κ →₀ α)) := by
  classical exact fun g₁ g₂ h ↦ sum_le_sum_index h (fun _ _ ↦ single_mono) (by simp)

lemma mapDomain_nonneg {f : ι → κ} (hg : 0 ≤ g) : 0 ≤ g.mapDomain f := by
  simpa using mapDomain_mono hg

lemma mapDomain_nonpos {f : ι → κ} (hg : g ≤ 0) : g.mapDomain f ≤ 0 := by
  simpa using mapDomain_mono hg

end Finsupp
