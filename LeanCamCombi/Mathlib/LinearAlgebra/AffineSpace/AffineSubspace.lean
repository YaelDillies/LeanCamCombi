import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# TODO

Kill `spanPoints`
-/

open Set

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

namespace AffineSubspace
variable {s : AffineSubspace k P} {x y z : P}

lemma mem_of_collinear (h : Collinear k {x, y, z}) (hx : x ∈ s) (hz : z ∈ s) : y ∈ s := sorry

end AffineSubspace

-- TODO: Prove that `SameRay` implies `Collinear`

@[simp] lemma affineSpan_insert_zero (s : Set V) :
    (affineSpan k (insert 0 s) : Set V) = Submodule.span k s := by
  refine subset_antisymm ?_ ?_
  · rw [← Submodule.span_insert_zero]
    exact affineSpan_subset_span
  let W : Submodule k V :=
    { carrier := affineSpan k (insert 0 s)
      add_mem' := fun {x y} hx hy ↦ by
        sorry
      zero_mem' := subset_affineSpan _ _ <| mem_insert ..
      smul_mem' := fun {a x} hx ↦ by
        simp only [SetLike.mem_coe]
        refine AffineSubspace.mem_of_collinear ?_ hx <| subset_affineSpan _ _ <| mem_insert ..
        sorry
         }
  change Submodule.span k s ≤ W
  exact Submodule.span_le.2 fun x hx ↦ subset_affineSpan _ _ <| subset_insert _ _ hx
