import Mathlib.Order.Partition.Finpartition

open Finset

namespace Finpartition
variable {α : Type*} [DecidableEq α] {s t u : Finset α} (P : Finpartition s) {a : α}

lemma eq_of_mem_parts (ht : t ∈ P.parts) (hu : u ∈ P.parts) (hat : a ∈ t) (hau : a ∈ u) : t = u :=
  P.disjoint.elim ht hu <| not_disjoint_iff.2 ⟨a, hat, hau⟩

end Finpartition
