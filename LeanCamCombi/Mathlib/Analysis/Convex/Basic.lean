import Mathlib.Analysis.Convex.Basic

open scoped BigOperators

open Finset

variable {𝕜 E ι : Type*} [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {m n : ℕ}

-- TODO: golf `AffineSubspace.convex`
example (s : AffineSubspace 𝕜 E) : Convex 𝕜 (s : Set E) := fun x hx y hy a b _ _ hab =>
  calc
    a • x + b • y = b • (y - x) + x := Convex.combo_eq_smul_sub_add hab
    _ ∈ s := s.2 _ hy hx hx
