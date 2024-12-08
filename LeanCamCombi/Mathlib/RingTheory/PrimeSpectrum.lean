import Mathlib.RingTheory.PrimeSpectrum

namespace PrimeSpectrum

variable {R} [CommSemiring R]

@[simp]
lemma zeroLocus_union_singleton_zero {s : Set R} :
    zeroLocus (s ∪ {0}) = zeroLocus s := by
  rw [zeroLocus_union, zeroLocus_singleton_zero, Set.inter_univ]

@[simp]
lemma zeroLocus_diff_singleton_zero {s : Set R} :
    zeroLocus (s \ {0}) = zeroLocus s := by
  rw [← zeroLocus_union_singleton_zero, ← zeroLocus_union_singleton_zero (s := s)]
  simp

end PrimeSpectrum
