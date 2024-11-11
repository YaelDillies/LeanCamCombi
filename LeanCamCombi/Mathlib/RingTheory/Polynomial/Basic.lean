import Mathlib.RingTheory.Polynomial.Basic

-- TODO: Replace in mathlib
lemma Polynomial.ker_mapRingHom' {R S} [CommRing R] [CommRing S] (f : R →+* S) :
    RingHom.ker (mapRingHom f) = (RingHom.ker f).map C := by
  rw [← Polynomial.ker_mapRingHom]
  rfl
