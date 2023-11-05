import Mathlib.LinearAlgebra.AffineSpace.Independent

open Finset
open scoped BigOperators

variable {𝕜 E ι : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] {p : ι → E} {w w₁ w₂ : ι → 𝕜}
  {s : Finset ι} {m n : ℕ}

lemma AffineIndependent.eq_zero_of_sum_eq_zero (hp : AffineIndependent 𝕜 p)
    (hw₀ : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w i • p i = 0) : ∀ i ∈ s, w i = 0 :=
  affineIndependent_iff.1 hp _ _ hw₀ hw₁

lemma AffineIndependent.eq_of_sum_eq_sum (hp : AffineIndependent 𝕜 p)
    (hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i) (hwp : ∑ i in s, w₁ i • p i = ∑ i in s, w₂ i • p i) :
    ∀ i ∈ s, w₁ i = w₂ i := by
  refine' fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero (w := w₁ - w₂) _ _ _ hi)
  all_goals simpa [sub_mul, sub_smul, sub_eq_zero]

lemma AffineIndependent.eq_zero_of_sum_eq_zero_subtype {s : Finset E}
    (hp : AffineIndependent 𝕜 ((↑) : s → E)) {w : E → 𝕜} (hw₀ : ∑ x in s, w x = 0)
    (hw₁ : ∑ x in s, w x • x = 0) : ∀ x ∈ s, w x = 0 := by
  rw [← sum_attach] at hw₀ hw₁
  exact fun x hx => hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _)

lemma AffineIndependent.eq_of_sum_eq_sum_subtype {s : Finset E}
    (hp : AffineIndependent 𝕜 ((↑) : s → E)) {w₁ w₂ : E → 𝕜} (hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i)
    (hwp : ∑ i in s, w₁ i • i = ∑ i in s, w₂ i • i) : ∀ i ∈ s, w₁ i = w₂ i := by
  refine' fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype (w := w₁ - w₂) _ _ _ hi)
  all_goals simpa [sub_mul, sub_smul, sub_eq_zero]
