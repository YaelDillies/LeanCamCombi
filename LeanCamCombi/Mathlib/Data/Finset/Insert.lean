import Mathlib.Data.Finset.Insert

namespace Finset
variable {α : Type*} [DecidableEq α]

instance Nontrivial.instDecidablePred : DecidablePred (Finset.Nontrivial (α := α)) :=
  inferInstanceAs (DecidablePred fun s ↦ ∃ a ∈ s, ∃ b ∈ s, a ≠ b)

end Finset
