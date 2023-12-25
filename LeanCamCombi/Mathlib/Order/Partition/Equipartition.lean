import Order.Partition.Equipartition
import Mathlib.Data.Set.Equitable

namespace Finpartition

variable {α : Type _} [DecidableEq α] {s : Finset α} {P : Finpartition s}

#print Finpartition.not_isEquipartition /-
@[simp]
theorem not_isEquipartition :
    ¬P.IsEquipartition ↔ ∃ a ∈ P.parts, ∃ b ∈ P.parts, Finset.card b + 1 < Finset.card a :=
  Set.not_equitableOn
-/

end Finpartition
