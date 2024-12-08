import Mathlib.RingTheory.PrimeSpectrum

open scoped Pointwise

namespace PrimeSpectrum
variable {R : Type*} [CommSemiring R] {r : R}

@[simp]
lemma zeroLocus_union_singleton_zero (s : Set R) : zeroLocus (s ∪ {0}) = zeroLocus s := by
  rw [zeroLocus_union, zeroLocus_singleton_zero, Set.inter_univ]

@[simp]
lemma zeroLocus_diff_singleton_zero (s : Set R) : zeroLocus (s \ {0}) = zeroLocus s := by
  rw [← zeroLocus_union_singleton_zero, ← zeroLocus_union_singleton_zero (s := s)]
  simp

lemma zeroLocus_smul_of_isUnit (hr : IsUnit r) (s : Set R) : zeroLocus (r • s) = zeroLocus s := by
  ext
  simp [Set.subset_def, ← Set.image_smul, Ideal.unit_mul_mem_iff_mem _ hr]

end PrimeSpectrum
