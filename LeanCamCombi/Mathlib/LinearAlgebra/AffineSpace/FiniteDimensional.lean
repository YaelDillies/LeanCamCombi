import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Finset
open scoped BigOperators

variable {𝕜 E ι : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι] {p : ι → E}

lemma AffineIndependent.card_le_finrank_succ (hp : AffineIndependent 𝕜 p) :
    Fintype.card ι ≤ FiniteDimensional.finrank 𝕜 (vectorSpan 𝕜 (Set.range p)) + 1 := by
  cases isEmpty_or_nonempty ι
  · simp [Fintype.card_eq_zero]
  rw [← tsub_le_iff_right]
  exact
    (affineIndependent_iff_le_finrank_vectorSpan _ _
          (tsub_add_cancel_of_le <| Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero).symm).1
      hp
