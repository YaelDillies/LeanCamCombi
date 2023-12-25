import Order.Partition.Finpartition

#align_import mathlib.order.partition.finpartition

open Finset

namespace Finpartition

variable {α : Type _} [DecidableEq α] {s t u : Finset α} (P : Finpartition s) {a : α}

#print Finpartition.eq_of_mem_parts /-
theorem eq_of_mem_parts (ht : t ∈ P.parts) (hu : u ∈ P.parts) (hat : a ∈ t) (hau : a ∈ u) : t = u :=
  P.Disjoint.elim ht hu <| not_disjoint_iff.2 ⟨a, hat, hau⟩
-/

end Finpartition

