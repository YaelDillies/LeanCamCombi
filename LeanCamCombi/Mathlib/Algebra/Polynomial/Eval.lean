import Mathlib.Algebra.Polynomial.Eval

namespace Polynomial

lemma mapRingHom_comp_C {R S} [CommRing R] [CommRing S] (f : R →+* S) : 
    (mapRingHom f).comp C = C.comp f := by ext; simp
