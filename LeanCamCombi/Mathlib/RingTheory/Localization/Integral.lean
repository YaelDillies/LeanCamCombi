import Mathlib.RingTheory.Localization.Integral

namespace Polynomial

lemma isLocalization {R} [CommRing R] (S : Submonoid R) (A) [CommRing A] [Algebra R A]
    [IsLocalization S A] :
    letI := (mapRingHom (algebraMap R A)).toAlgebra; IsLocalization (S.map C) A[X] := by
  letI := (mapRingHom (algebraMap R A)).toAlgebra
  constructor
  · rintro ⟨_, r, hr, rfl⟩
    simpa [RingHom.algebraMap_toAlgebra] using (IsLocalization.map_units A ⟨r, hr⟩).map C
  · intro z
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec S z
    refine ⟨⟨IsLocalization.integerNormalization S z, _, b, b.2, rfl⟩, ?_⟩
    ext i
    simp only [RingHom.algebraMap_toAlgebra, coe_mapRingHom, map_C, coeff_mul_C, coeff_map, hb,
      mul_comm, Algebra.smul_def]
  · intros x y e
    rw [← sub_eq_zero, ← map_sub, RingHom.algebraMap_toAlgebra, ← RingHom.mem_ker,
      Polynomial.ker_mapRingHom, Ideal.mem_map_C_iff] at e
    simp only [coeff_sub, RingHom.mem_ker, map_sub, sub_eq_zero,
      IsLocalization.eq_iff_exists S] at e
    choose c hc using e
    refine ⟨⟨_, _, ((x.support ∪ y.support).prod c).2, rfl⟩, ?_⟩
    ext i
    simp only [coeff_C_mul]
    by_cases hi : i ∈ x.support ∪ y.support
    · obtain ⟨k, e⟩ := Finset.dvd_prod_of_mem c hi
      simp only [e, mul_comm _ k, Submonoid.coe_mul _ k, mul_assoc, hc]
    · simp only [Finset.mem_union, mem_support_iff, ne_eq, not_or, not_not] at hi
      simp [hi.1, hi.2]

end Polynomial
