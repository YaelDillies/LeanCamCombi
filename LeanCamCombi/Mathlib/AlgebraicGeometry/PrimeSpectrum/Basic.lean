import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import LeanCamCombi.Mathlib.RingTheory.Localization.Integral

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

lemma PrimeSpectrum.comap_eq_specComap (f : R →+* S) :
  comap f = f.specComap := rfl

lemma PrimeSpectrum.comap_eq_specComap' (f : R →+* S) (x) :
  comap f x = f.specComap x := rfl
open Polynomial

namespace PrimeSpectrum

open Localization in
lemma comap_C_eq_comap_localization_union_comap_quotient
    {R : Type*} [CommRing R] (s : Set (PrimeSpectrum R[X])) (c : R) :
    .comap C '' s =
      comap (algebraMap R (Away c)) '' (comap C ''
        (comap (mapRingHom (algebraMap R (Away c))) ⁻¹' s)) ∪
      comap (Ideal.Quotient.mk (.span {c})) '' (comap C ''
        (comap (mapRingHom (Ideal.Quotient.mk _)) ⁻¹' s)) := by
  rw [Set.union_comm]
  simp_rw [← Set.image_comp, ← ContinuousMap.coe_comp, ← comap_comp, ← mapRingHom_comp_C,
    comap_comp, ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range,
    ← Set.image_union, ← Set.inter_union_distrib_left]
  letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
  suffices Set.range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) =
      (Set.range (comap (algebraMap R[X] (Away c)[X])))ᶜ by
    rw [this, RingHom.algebraMap_toAlgebra, Set.compl_union_self, Set.inter_univ]
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj, localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

end PrimeSpectrum
