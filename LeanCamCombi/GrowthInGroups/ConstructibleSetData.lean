import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import LeanCamCombi.Mathlib.Algebra.Ring.Hom.Defs
import LeanCamCombi.GrowthInGroups.WithBotSucc

open Finset PrimeSpectrum
open scoped Polynomial

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-! ### Bare types -/

variable (R) in
abbrev ConstructibleSetData := Finset (Σ n, R × (Fin n → R))

namespace ConstructibleSetData

def map [DecidableEq S] (f : R →+* S) (s : ConstructibleSetData R) : ConstructibleSetData S :=
  s.image <| Sigma.map id fun _n (r, g) ↦ (f r, f ∘ g)

@[simp] lemma map_id [DecidableEq R] (s : ConstructibleSetData R) : s.map (.id _) = s := by
  unfold map Sigma.map; simp [RingHom.coe_id]

lemma map_comp [DecidableEq S] [DecidableEq T] (f : S →+* T) (g : R →+* S)
    (s : ConstructibleSetData R) : s.map (f.comp g) = (s.map g).map f := by
  unfold map Sigma.map; simp [image_image, Function.comp_def]

/-! ### Rings -/

def toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) :=
  ⋃ x ∈ S, zeroLocus (Set.range x.2.2) \ zeroLocus {x.2.1}

@[simp]
lemma toSet_map [DecidableEq S] (f : R →+* S) (s : ConstructibleSetData R) :
    (s.map f).toSet = comap f ⁻¹' s.toSet := by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp only [id_eq, Set.preimage_iUnion, Set.preimage_diff, preimage_comap_zeroLocus,
    Set.image_singleton, ← Set.range_comp]
  rfl

def degBound (S : ConstructibleSetData R[X]) : ℕ := S.sup fun e ↦ ∑ i, (e.2.2 i).degree.succ

def mvDegBound {σ} (S : ConstructibleSetData (MvPolynomial σ R)) : ℕ :=
  S.sup fun e ↦ ∑ i, (e.2.2 i).totalDegree.succ

end ConstructibleSetData
