import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Topology
import LeanCamCombi.Mathlib.Analysis.Convex.Between

open AffineMap Filter Finset Set
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

lemma IsInSight.of_convexHull_of_pos {ι : Type*} {t : Finset ι} {a : ι → V} {w : ι → 𝕜}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1) (ha : ∀ i ∈ t, a i ∈ s)
    (hx : x ∉ convexHull 𝕜 s) (hw : IsInSight 𝕜 (convexHull 𝕜 s) x (∑ i ∈ t, w i • a i)) {i : ι}
    (hi : i ∈ t) (hwi : 0 < w i) : IsInSight 𝕜 (convexHull 𝕜 s) x (a i) := sorry

end Module

section Real
variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [TopologicalAddGroup V]
  [ContinuousSMul ℝ V] {s : Set V} {x y z : V}

lemma IsClosed.exists_wbtw_isInSight (hs : IsClosed s) (hy : y ∈ s) (x : V) :
    ∃ z ∈ s, Wbtw ℝ x z y ∧ IsInSight ℝ s x z := by
  let t : Set ℝ := Ici 0 ∩ lineMap x y ⁻¹' s
  have ht₁ : 1 ∈ t := by simpa [t]
  have ht : BddBelow t := bddBelow_Ici.inter_of_left
  let δ : ℝ := sInf t
  have hδ₁ : δ ≤ 1 := csInf_le ht ht₁
  obtain ⟨hδ₀, hδ⟩ : 0 ≤ δ ∧ lineMap x y δ ∈ s :=
    (isClosed_Ici.inter <| hs.preimage lineMap_continuous).csInf_mem ⟨1, ht₁⟩ ht
  refine ⟨lineMap x y δ, hδ, wbtw_lineMap_iff.2 <| .inr ⟨hδ₀, hδ₁⟩, ?_⟩
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, -, h⟩
  replace hδ₀ : 0 < δ := hδ₀.lt_of_ne' <| by rintro hδ₀; simp [hδ₀] at h
  replace hε₁ : ε < 1 := hε₁.lt_of_ne <| by rintro rfl; simp at h
  rw [lineMap_lineMap_right] at hε
  exact (csInf_le ht ⟨mul_nonneg hε₀ hδ₀.le, hε⟩).not_lt <| mul_lt_of_lt_one_left hδ₀ hε₁

lemma IsInSight.mem_convexHull_isInSight (hx : x ∉ convexHull ℝ s) (hy : y ∈ convexHull ℝ s)
    (hxy : IsInSight ℝ (convexHull ℝ s) x y) :
    y ∈ convexHull ℝ {z ∈ s | IsInSight ℝ (convexHull ℝ s) x z} := by
  classical
  obtain ⟨ι, _, w, a, hw₀, hw₁, ha, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hy
  rw [← Fintype.sum_subset (s := {i | w i ≠ 0})
    fun i hi ↦ mem_filter.2 ⟨mem_univ _, left_ne_zero_of_smul hi⟩]
  exact (convex_convexHull ..).sum_mem (fun i _ ↦ hw₀ _) (by rwa [sum_filter_ne_zero])
    fun i hi ↦ subset_convexHull _ _ ⟨ha _, IsInSight.of_convexHull_of_pos (fun _ _ ↦ hw₀ _) hw₁
      (by simpa) hx hxy (mem_univ _) <| (hw₀ _).lt_of_ne' (mem_filter.1 hi).2⟩

lemma IsClosed.convexHull_subset_affineSpan_isInSight (hs : IsClosed (convexHull ℝ s))
    (hx : x ∉ convexHull ℝ s) :
    convexHull ℝ s ⊆ affineSpan ℝ ({x} ∪ {y ∈ s | IsInSight ℝ (convexHull ℝ s) x y}) := by
  rintro y hy
  obtain ⟨z, hz, hxzy, hxz⟩ := hs.exists_wbtw_isInSight hy x
  -- TODO: `calc` doesn't work with `∈` :(
  exact AffineSubspace.right_mem_of_wbtw hxzy (subset_affineSpan _ _ <| subset_union_left rfl)
    (affineSpan_mono _ subset_union_right <| convexHull_subset_affineSpan _ <|
      hxz.mem_convexHull_isInSight hx hz) (ne_of_mem_of_not_mem hz hx).symm

end Real
