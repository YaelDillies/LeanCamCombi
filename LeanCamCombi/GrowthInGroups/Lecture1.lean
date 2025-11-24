/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Combinatorics.Additive.VerySmallDoubling
import Mathlib.Geometry.Group.Growth.LinearLowerBound
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import LeanCamCombi.Util

/-!
# Growth in Groups - Lecture 1

This file contains a Lean formalisation of the statements and proofs given in lecture 1 of the ETH
course Growth in Groups lectured by Simon Machado in autumn/winter 2024.

## References

[Lecture notes by Simon Machado](https://sites.google.com/view/simonmachado/teaching)
-/

open Finset Fintype Group MulOpposite Real
open scoped Combinatorics.Additive MatrixGroups Pointwise

namespace GrowthInGroups.Lecture1
variable {G : Type*} [Group G] [DecidableEq G] {A X : Finset G} {n : ℕ} {K : ℝ}

/-- The growth of a set generating an infinite group is at least linear. -/
lemma fact_1_1_1 [Infinite G] (hX₁ : 1 ∈ X) (hXgen : Subgroup.closure (X : Set G) = ⊤) (n : ℕ) :
    n + 1 ≤ #(X ^ n) := add_one_le_card_pow hX₁ (by simp [hXgen, Set.infinite_univ]) _

/-- The growth of a set is at most exponential. -/
lemma fact_1_1_2 : #(X ^ n) ≤ #X ^ n := card_pow_le

variable (G) in
/-- A group **has polynomial growth** if any (equivalently, all) of its finite symmetric sets
has polynomial growth. -/
def HasPolynomialGrowth : Prop :=
  ∃ X : Finset G, X⁻¹ = X ∧ Subgroup.closure (X : Set G) = ⊤ ∧ ∃ d, ∀ n ≥ 2, #(X ^ n) ≤ n ^ d

/-- **Gromov's theorem**.

A group has polynomial growth iff it's virtually nilpotent. -/
lemma theorem_1_2 : HasPolynomialGrowth G ↔ IsVirtuallyNilpotent G := showcased

lemma fact_1_3 [Fintype G] (hn : X ^ n = univ) : log (card G) / log #X ≤ n := by
  obtain rfl | hX := X.eq_empty_or_nonempty
  · simp
  refine div_le_of_le_mul₀ (log_nonneg <| by simpa) (by positivity) ?_
  rw [← log_pow, ← Nat.cast_pow, ← card_univ, ← hn]
  gcongr
  exact card_pow_le

/-- **Babai's conjecture**.

For all finite sets `X` generating a simple group `G`, there exists a universal polynomial
(in `log |G|`) upper bound to the number of steps `X` takes to generate `G`. -/
lemma conjecture_1_4 :
    ∃ Cᵤ ≥ 0, ∃ dᵤ ≥ 0,
      ∀ {G} [Group G] [IsSimpleGroup G] [Fintype G] [DecidableEq G] (X : Finset G)
        (_hX₁ : 1 ∈ X) (_hXsymm : X⁻¹ = X) (_hXclos : Subgroup.closure (X : Set G) = ⊤),
          ∃ m : ℕ, m ≤ Cᵤ * log (card G) ^ dᵤ ∧ X ^ m = univ := showcased

-- Not even trying to state the collar lemma

open scoped Classical in
/-- An auxiliary lemma used in the proof of the collar theorem. -/
lemma proposition_1_7 :
    ∃ ε > 0, ∀ X : Finset SL(2, ℝ), #(X ^ 2) ≤ 1000 * #X → (∀ M ∈ X, ∀ i j, |M i j| ≤ ε) →
      ∃ A : Subgroup SL(2, ℝ), IsMulCommutative A ∧
        ∃ a : Fin 10000000 → SL(2, ℝ), (X : Set SL(2, ℝ)) ⊆ ⋃ i, a i • A := showcased

/-- The **Breuillard-Green-Tao theorem**. -/
lemma theorem_1_8 :
    ∃ C > 0, ∀ {G} [Group G] [DecidableEq G] (A : Finset G) (_hA : σₘ[A] ≤ K),
      ∃ (N : Subgroup G) (D : Subgroup N) (_hD : D.Normal),
        upperCentralSeries (N⧸ D) C = ⊤ ∧ ((↑) '' (D : Set N) : Set G) ⊆ (A / A) ^ 4 ∧
          ∃ a : Fin C → G, (A : Set G) ⊆ ⋃ i, a i • N := showcased

open scoped Classical in
/-- The **product theorem**, due Breuillard-Green-Tao and Pyber-Szabo.

A set in `SLₙ(k)` either has big tripling or is very big. In other words, there is no small
tripling, except in trivial situations. -/
lemma theorem_1_9 :
    ∃ δ > 0, ∃ ε > 0,
      ∀ k [Field k] [Fintype k] [DecidableEq k] (A : Finset SL(n, k))
        (_hAgen : Subgroup.closure (A : Set SL(n, k)) = ⊤),
          #A ^ (1 + δ) ≤ #(A ^ 3) ∨ card SL(n, k) ^ (1 - ε) ≤ #A := proved_later

open MulAction in
open scoped RightActions in
/-- A non-empty set `A` with no doubling is the coset of a subgroup `H`.

Precisely, `H` can be taken to be the stabiliser of `A` and `A` then is both a left and right coset
of `H`. -/
lemma fact_1_10 (hA : #(A * A) ≤ #A) :
    ∃ H : Subgroup G, ∀ a ∈ A, a •> (H : Set G) = A ∧ (H : Set G) <• a = A :=
  ⟨stabilizer G A, fun _a ha ↦
    ⟨smul_stabilizer_of_no_doubling hA ha, op_smul_stabilizer_of_no_doubling hA ha⟩⟩

open scoped Classical RightActions in
/-- A set `A` of tripling strictly less than three halves can be contained in a coset of a subgroup
`H` of size strictly `|H| < 3/2 |A|`.

One can furthermore arrange for `A` to lie in the centraliser of `H`. -/
lemma lemma_1_11 (hA : #(A * A) < (3 / 2 : ℚ) * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H),
      (card H : ℚ≥0) < 3 / 2 * #A ∧ ∀ a ∈ A, (A : Set G) ⊆ a • H ∧ a • (H : Set G) = H <• a :=
  doubling_lt_three_halves hA

end GrowthInGroups.Lecture1
