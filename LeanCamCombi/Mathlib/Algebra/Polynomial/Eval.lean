import Mathlib.Algebra.Polynomial.Eval

namespace Polynomial

lemma mapRingHom_comp_C {R S} [CommRing R] [CommRing S] (f : R →+* S) :
    (mapRingHom f).comp C = C.comp f := by ext; simp

variable {R S : Type*} [Semiring R] [Semiring S]

-- TODO: Rename `coeff_map` to `coeff_map_apply`?
lemma coeff_map_eq_comp (p : R[X]) (f : R →+* S) : (p.map f).coeff = f ∘ p.coeff := by
  ext n; exact coeff_map ..
