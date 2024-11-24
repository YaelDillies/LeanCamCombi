import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Lattice.Basic

namespace Finset
variable {α : Type*} [DecidableEq α] {s t : Finset α}

@[simp] lemma union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  mod_cast Set.union_nonempty (α := α) (s := s) (t := t)

end Finset
