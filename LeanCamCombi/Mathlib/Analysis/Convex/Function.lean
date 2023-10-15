import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.Extr

variable {𝕜 E β : Type*}

section LinearOrderedField
variable [LinearOrderedField 𝕜] [OrderedAddCommMonoid β] [AddCommMonoid E] [SMul 𝕜 E]

section SMul
variable [SMul 𝕜 β] {s : Set E}

end SMul

section Module
variable [Module 𝕜 β] [OrderedSMul 𝕜 β] {f : E → β} {s : Set E} {x y : E}

/-- A strictly convex function admits at most one global minimum. -/
lemma StrictConvexOn.eq_of_isMinOn (hf : StrictConvexOn 𝕜 s f) (hfx : IsMinOn f s x)
    (hfy : IsMinOn f s y) (hx : x ∈ s) (hy : y ∈ s) : x = y := by
  by_contra hxy
  let z := (2 : 𝕜)⁻¹ • x + (2 : 𝕜)⁻¹ • y
  have hz : z ∈ s := hf.1 hx hy (by norm_num) (by norm_num) $ by norm_num
  refine lt_irrefl (f z) ?_
  calc
    f z < _ := hf.2 hx hy hxy (by norm_num) (by norm_num) $ by norm_num
    _ ≤ (2 : 𝕜)⁻¹ • f z + (2 : 𝕜)⁻¹ • f z := add_le_add (smul_le_smul_of_nonneg (hfx hz) $ by norm_num) (smul_le_smul_of_nonneg (hfy hz) $ by norm_num)
    _ = f z := by rw [←_root_.add_smul]; norm_num

/-- A strictly concave function admits at most one global maximum. -/
lemma StrictConcaveOn.eq_of_isMaxOn (hf : StrictConcaveOn 𝕜 s f) (hfx : IsMaxOn f s x)
    (hfy : IsMaxOn f s y) (hx : x ∈ s) (hy : y ∈ s) : x = y :=
  hf.dual.eq_of_isMinOn hfx hfy hx hy

end Module
end LinearOrderedField
