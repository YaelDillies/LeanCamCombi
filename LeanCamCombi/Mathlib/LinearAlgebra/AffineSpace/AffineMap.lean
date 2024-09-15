import Mathlib.LinearAlgebra.AffineSpace.AffineMap

namespace AffineMap
variable {k V1 P1 : Type*} [Ring k] [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1] {p₀ p₁ : P1}

@[simp] lemma lineMap_lineMap_right (c d : k) :
    lineMap p₀ (lineMap p₀ p₁ c) d = lineMap p₀ p₁ (d * c) := by
  simp [lineMap_apply, mul_smul]

-- @[simp] lemma lineMap_lineMap_left (c d : k) :
--     lineMap (lineMap p₀ p₁ c) p₁ d = lineMap p₀ p₁ (1 - (1 - d) * c) := by
--   simp [lineMap_apply, mul_smul]; sorry

end AffineMap
