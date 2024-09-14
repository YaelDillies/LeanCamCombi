import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Topology
import LeanCamCombi.Mathlib.LinearAlgebra.AffineSpace.AffineMap

open AffineMap Filter Set
open scoped Topology

variable {𝕜 V P : Type*}

section AddTorsor
variable [LinearOrderedField 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
  {s t : Set P} {x y z : P}

variable (𝕜) in
def IsInSight (s : Set P) (x y : P) : Prop := ∀ ⦃z⦄, z ∈ s → ¬ Sbtw 𝕜 x z y

@[simp, refl] lemma IsInSight.rfl : IsInSight 𝕜 s x x := by simp [IsInSight]

lemma isInSight_comm : IsInSight 𝕜 s x y ↔ IsInSight 𝕜 s y x := by simp [IsInSight, sbtw_comm]

@[symm] alias ⟨IsInSight.symm, _⟩ := isInSight_comm

lemma IsInSight.mono (hst : s ⊆ t) (ht : IsInSight 𝕜 t x y) : IsInSight 𝕜 s x y :=
  fun _z hz ↦ ht <| hst hz

-- lemma IsInSight.eq_of_wbtw (hxy : IsInSight 𝕜 s x y) (hz : z ∈ s) (hxyz : Wbtw 𝕜 x y z) :
--     x = y := hxyz.eq_of_not_sbtw

end AddTorsor

section Module
variable [LinearOrderedField 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V]
  {s : Set V} {x y z : V}

lemma IsOpen.eq_of_isInSight_of_left_mem (hs : IsOpen s) (hsxy : IsInSight 𝕜 s x y) (hx : x ∈ s) :
    x = y := by
  by_contra! hxy
  have hmem : ∀ᶠ (δ : 𝕜) in 𝓝[>] 0, lineMap x y δ ∈ s :=
    lineMap_continuous.continuousWithinAt.eventually_mem (hs.mem_nhds (by simpa))
  have hsbtw : ∀ᶠ (δ : 𝕜) in 𝓝[>] 0, Sbtw 𝕜 x (lineMap x y δ) y := by
    simpa [sbtw_lineMap_iff, eventually_and, hxy] using
      ⟨eventually_nhdsWithin_of_forall fun δ hδ ↦ hδ,
        eventually_lt_of_tendsto_lt zero_lt_one nhdsWithin_le_nhds⟩
  suffices h : ∀ᶠ (_δ : 𝕜) in 𝓝[>] 0, False by obtain ⟨_, ⟨⟩⟩ := h.exists
  filter_upwards [hmem, hsbtw] with δ hmem hsbtw
  exact hsxy hmem hsbtw

end Module

section Real
variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [TopologicalAddGroup V]
  [ContinuousSMul ℝ V] {s : Set V} {x y z : V}

lemma IsClosed.exists_isInSight (hs : IsClosed s) (hy : y ∈ s) :
    ∃ z ∈ s, Wbtw ℝ x z y ∧ IsInSight ℝ s x z := by
  let t : Set ℝ := Ici 0 ∩ lineMap x y ⁻¹' s
  have ht₁ : 1 ∈ t := by simpa [t]
  have ht : BddBelow t := bddBelow_Ici.inter_of_left
  let δ : ℝ := sInf t
  have hδ₁ : δ ≤ 1 := csInf_le bddBelow_Ici.inter_of_left ht₁
  obtain ⟨hδ₀, hδ⟩ : 0 ≤ δ ∧ lineMap x y δ ∈ s :=
    (isClosed_Ici.inter <| hs.preimage lineMap_continuous).csInf_mem ⟨1, ht₁⟩ ht
  refine ⟨lineMap x y δ, hδ, wbtw_lineMap_iff.2 <| .inr ⟨hδ₀, hδ₁⟩, ?_⟩
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, -, h⟩
  replace hδ₀ : 0 < δ := hδ₀.lt_of_ne' <| by rintro hδ₀; simp [hδ₀] at h
  replace hε₁ : ε < 1 := hε₁.lt_of_ne <| by rintro rfl; simp at h
  rw [lineMap_lineMap] at hε
  exact (csInf_le ht ⟨mul_nonneg hε₀ hδ₀.le, hε⟩).not_lt <| mul_lt_of_lt_one_left hδ₀ hε₁

-- lemma subset_coneHull :

end Real
