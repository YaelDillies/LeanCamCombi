import LeanCamCombi.Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {A B B₁ B₂ : Finset G}

@[to_additive] def mulVCDim (A B : Finset G) : ℕ := ((B / A).image (· • A ∩ B)).vcDim

@[to_additive (attr := gcongr)]
lemma mulVCDim_mono (hB : B₁ ⊆ B₂) : mulVCDim A B₁ ≤ mulVCDim A B₂ := by
  refine sup_mono ?_
  simp only [subset_iff, mem_shatterer, Shatters, mem_image, exists_exists_and_eq_and]
  rintro C hC D hD
  have hCB : C ⊆ B₁ := by
    obtain ⟨x, -, h⟩ := hC fun x hx ↦ hx
    exact (inter_eq_left.1 h).trans inter_subset_right
  obtain ⟨x, hx, rfl⟩ := hC hD
  refine ⟨x, div_subset_div_right hB hx, ?_⟩
  rw [inter_left_comm, inter_eq_left.2 <| hCB.trans hB, inter_left_comm, inter_eq_left.2 hCB]

end Finset
