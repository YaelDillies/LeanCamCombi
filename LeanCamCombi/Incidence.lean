import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

variable {𝕜 α : Type*}

namespace IncidenceAlgebra
variable (α) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [BoundedOrder α] [LocallyFiniteOrder α]
  [DecidableEq α]

/-- The Euler characteristic of a finite bounded order. -/
def eulerChar : 𝕜 := mu 𝕜 (⊥ : α) ⊤

end IncidenceAlgebra
