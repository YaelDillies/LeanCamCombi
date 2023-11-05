import Mathlib.Data.Nat.Lattice

namespace Nat
variable {ι : Sort*}

@[simp]
lemma iInf_empty [IsEmpty ι] (f : ι → ℕ) : (⨅ i : ι, f i) = 0 := by
  rw [iInf, Set.range_eq_empty, sInf_empty]

@[simp]
lemma iInf_const_zero : (⨅ i : ι, 0) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact iInf_empty _
  · exact ciInf_const

end Nat
