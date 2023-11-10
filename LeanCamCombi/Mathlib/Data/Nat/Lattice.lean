import Mathlib.Data.Nat.Lattice

namespace Nat
variable {ι : Sort*}

@[simp]
lemma iInf_const_zero : (⨅ i : ι, 0) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact iInf_of_empty _
  · exact ciInf_const

end Nat
