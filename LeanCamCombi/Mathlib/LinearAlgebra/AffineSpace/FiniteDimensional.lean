import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

namespace AffineSubspace
variable {s : AffineSubspace k P} {x y z : P}

lemma mem_of_collinear (h : Collinear k {x, y, z}) (hx : x ∈ s) (hz : z ∈ s) : y ∈ s := sorry

end AffineSubspace

-- TODO: Prove that `SameRay` implies `Collinear`
