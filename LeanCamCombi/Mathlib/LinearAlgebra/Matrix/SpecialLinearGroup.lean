import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup
variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

instance [Fintype R] [DecidableEq R] : Fintype (SpecialLinearGroup n R) := Subtype.fintype _

end Matrix.SpecialLinearGroup
