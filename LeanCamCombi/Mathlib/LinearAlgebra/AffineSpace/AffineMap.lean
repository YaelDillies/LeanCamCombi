import Mathlib.LinearAlgebra.AffineSpace.AffineMap

namespace AffineMap
variable {k V1 P1 : Type*} [Ring k] [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1] {p₀ p₁ : P1}

lemma lineMap_lineMap (c d : k) : lineMap p₀ (lineMap p₀ p₁ c) d = lineMap p₀ p₁ (d * c) := by
  simp [lineMap_apply, mul_smul]

end AffineMap
