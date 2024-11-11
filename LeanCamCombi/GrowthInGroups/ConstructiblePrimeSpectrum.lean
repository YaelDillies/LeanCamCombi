import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.RingTheory.PrimeSpectrum


variable (R) {n : ℕ} [CommRing R]

namespace PrimeSpectrum

section ConstructibleComponent

structure ConstructibleComponent (n : ℕ) where
  f : R
  g : Fin n → R

variable {R} (S T : ConstructibleComponent R n)

def ConstructibleComponent.toSet : Set (PrimeSpectrum R) :=
  zeroLocus (Set.range S.g) \ zeroLocus {S.f}

end ConstructibleComponent

section Polynomial

open Polynomial Set

variable {R} (S : ConstructibleComponent R[X] n)

def ConstructibleComponent.coeffSubmodule : Submodule ℤ R :=
  Submodule.span ℤ (⋃ i, range (S.g i).coeff)

variable (n) in
abbrev ConstructibleComponent.DegreeType := (Fin n → WithBot ℕ) ×ₗ Prop

def ConstructibleComponent.degree : DegreeType n :=
  (Polynomial.degree ∘ S.g,
    ¬ ∃ i, IsUnit (S.g i).leadingCoeff ∧ ∀ j, S.g j ≠ 0 → (S.g i).degree ≤ (S.g j).degree)

def ConstructibleComponent.complexityBound : ℕ := ∑ i, (S.g i).natDegree

def ConstructibleComponent.exponentBound : ℕ := S.complexityBound ^ S.complexityBound

end Polynomial

end PrimeSpectrum
