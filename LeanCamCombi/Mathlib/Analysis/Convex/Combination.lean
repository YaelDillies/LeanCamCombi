import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import LeanCamCombi.Mathlib.LinearAlgebra.AffineSpace.Independent

open Finset
open scoped BigOperators

variable {𝕜 E ι : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {m n : ℕ}

lemma AffineIndependent.subset_convexHull_inter {X : Finset E}
    (hX : AffineIndependent 𝕜 ((↑) : X → E)) {Y₁ Y₂ : Finset E} (hY₁ : Y₁ ⊆ X)
    (hY₂ : Y₂ ⊆ X) :
    convexHull 𝕜 (Y₁ : Set E) ∩ convexHull 𝕜 (Y₂ : Set E) ⊆ convexHull 𝕜 (Y₁ ∩ Y₂ : Set E) := by
  classical
  rintro x ⟨hx₁, hx₂⟩
  rw [← coe_inter]
  rw [Finset.convexHull_eq] at hx₁ hx₂
  rcases hx₁ with ⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩
  rcases hx₂ with ⟨w₂, h₁w₂, h₂w₂, h₃w₂⟩
  rw [centerMass_eq_of_sum_1 _ _ h₂w₁] at h₃w₁
  rw [centerMass_eq_of_sum_1 _ _ h₂w₂] at h₃w₂
  dsimp at h₃w₁ h₃w₂
  let w : E → 𝕜 := by
    intro x
    apply (if x ∈ Y₁ then w₁ x else 0) - if x ∈ Y₂ then w₂ x else 0
  have h₁w : ∑ i in X, w i = 0 := by
    rw [Finset.sum_sub_distrib, ← sum_filter, filter_mem_eq_inter, ← sum_filter,
      filter_mem_eq_inter, Finset.inter_eq_right.2 hY₁, Finset.inter_eq_right.2 hY₂,
      h₂w₁, h₂w₂]
    simp only [sub_self]
  have : ∑ i : E in X, w i • i = 0 := by
    simp only [sub_smul, zero_smul, ite_smul, Finset.sum_sub_distrib, ← Finset.sum_filter, h₃w₁,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hY₁, Finset.inter_eq_right.2 hY₂, h₃w₂,
      sub_self]
  have hX' := hX.eq_zero_of_sum_eq_zero_subtype h₁w this
  have t₁ : ∀ x, x ∈ Y₁ → x ∉ Y₂ → w₁ x = 0 := by
    intro x hx₁ hx₂
    have : ite (x ∈ Y₁) (w₁ x) 0 - ite (x ∈ Y₂) (w₂ x) 0 = 0 := hX' _ (hY₁ hx₁)
    simpa [hx₁, hx₂] using this
  have h₄w₁ : ∑ y : E in Y₁ ∩ Y₂, w₁ y = 1 := by
    rw [Finset.sum_subset (Finset.inter_subset_left Y₁ Y₂), h₂w₁]
    rintro x
    simp_intro hx₁ hx₂
    exact t₁ x hx₁ hx₂
  rw [Finset.convexHull_eq]
  refine' ⟨w₁, _, h₄w₁, _⟩
  · simp only [and_imp, Finset.mem_inter]
    exact fun y hy₁ _ ↦ h₁w₁ y hy₁
  · rw [Finset.centerMass_eq_of_sum_1 _ _ h₄w₁]
    dsimp only [id.def]
    rw [Finset.sum_subset (Finset.inter_subset_left Y₁ Y₂), h₃w₁]
    rintro x
    simp_intro hx₁ hx₂
    exact Or.inl $ t₁ x hx₁ hx₂

/-- If an affine independent finset is contained in the convex hull of another finset, then it is
smaller than that finset. -/
lemma AffineIndependent.card_le_card_of_subset_convexHull {X Y : Finset E}
    (hX : AffineIndependent 𝕜 ((↑) : X → E)) (hXY : (X : Set E) ⊆ convexHull 𝕜 ↑Y) :
    X.card ≤ Y.card := by
  obtain rfl | h₁ := X.eq_empty_or_nonempty
  · simp
  obtain rfl | h₂ := Y.eq_empty_or_nonempty
  · simp only [Finset.coe_empty, convexHull_empty, Set.subset_empty_iff, Finset.coe_eq_empty] at hXY
    subst hXY
    rfl
  have X_card_pos : 1 ≤ X.card := h₁.card_pos
  have X_eq_succ : Fintype.card (X : Set E) = X.card - 1 + 1 := by
    simp [Nat.sub_add_cancel ‹1 ≤ X.card›]
  have Y_card_pos : 1 ≤ Y.card := h₂.card_pos
  have Y_eq_succ : Fintype.card (Y : Set E) = Y.card - 1 + 1 := by
    simp [Nat.sub_add_cancel ‹1 ≤ Y.card›]
  have direction_le := AffineSubspace.direction_le (affineSpan_mono 𝕜 hXY)
  rw [affineSpan_convexHull] at direction_le
  letI : FiniteDimensional 𝕜 (vectorSpan 𝕜 (Y : Set E)) :=
    finiteDimensional_vectorSpan_of_finite _ Y.finite_toSet
  rw [direction_affineSpan, direction_affineSpan] at direction_le
  have finrank_le := Submodule.finrank_le_finrank_of_le direction_le
  erw [← @Subtype.range_coe _ (X : Set E), ← @Subtype.range_coe _ (Y : Set E),
    hX.finrank_vectorSpan X_eq_succ] at finrank_le
  have := le_trans finrank_le (finrank_vectorSpan_range_le 𝕜 ((↑) : Y → E) Y_eq_succ)
  rwa [tsub_le_tsub_iff_right] at this
  exact Y_card_pos
