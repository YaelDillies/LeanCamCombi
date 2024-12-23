import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.SuccPred.WithBot

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

open scoped Classical in
/-- Remove the zero polynomials from the data of a constructible set. -/
noncomputable def reduce (S : ConstructibleSetData R) : ConstructibleSetData R :=
  S.image fun ⟨_, r, f⟩ ↦ ⟨#{x | f x ≠ 0}, r, f ∘ Subtype.val ∘ (Finset.equivFin _).symm⟩

def toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) :=
  ⋃ x ∈ S, zeroLocus (Set.range x.2.2) \ zeroLocus {x.2.1}

@[simp]
lemma toSet_reduce (S : ConstructibleSetData R) : S.reduce.toSet = S.toSet := by
  classical
  unfold toSet reduce
  rw [Finset.set_biUnion_finset_image]
  congr! 4 with y hy
  simp only [Set.range_comp, ne_eq, Equiv.range_eq_univ, Set.image_univ,
    Subtype.range_coe_subtype, mem_filter, mem_univ, true_and]
  show zeroLocus (y.2.2 '' (y.2.2 ⁻¹' {0}ᶜ)) = _
  rw [Set.image_preimage_eq_inter_range, ← Set.diff_eq_compl_inter,
    zeroLocus_diff_singleton_zero]

@[simp]
lemma toSet_map [DecidableEq S] (f : R →+* S) (s : ConstructibleSetData R) :
    (s.map f).toSet = comap f ⁻¹' s.toSet := by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp only [id_eq, Set.preimage_iUnion, Set.preimage_diff, preimage_comap_zeroLocus,
    Set.image_singleton, ← Set.range_comp]
  rfl

def degBound (S : ConstructibleSetData R[X]) : ℕ := S.sup fun e ↦ ∑ i, (e.2.2 i).degree.succ

end ConstructibleSetData
