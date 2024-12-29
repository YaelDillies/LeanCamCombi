import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import LeanCamCombi.Mathlib.RingTheory.Localization.Integral

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

namespace PrimeSpectrum

lemma coe_comap (f : R →+* S) : comap f = f.specComap := rfl

lemma comap_apply (f : R →+* S) (x) : comap f x = f.specComap x := rfl

open Localization Polynomial Set

variable {R : Type*} [CommRing R] (c : R)

lemma range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk (c : R) :
    letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
    (range (comap (algebraMap R[X] (Away c)[X])))ᶜ
      = range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) := by
  letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj, localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

end PrimeSpectrum
