/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import LeanCamCombi.Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure

/-!
# Bernoulli random variables

This file defines the binomial random distribution on a set. For a set `u : Set ι` and `p` between
`0` and `1`, this is the measure on `Set ι` such that each `i ∈ u` belongs to the random set with
probability `p`, and each `i ∉ u` doesn't belong to it.

## Notation

`Ber(u, p)` is the product of `p`-Bernoulli distributions on `u`.

## TODO

Add the characteristic predicate for a random variable to follow the Bernoulli distribution.
-/

open MeasureTheory Measure unitInterval
open scoped Finset

namespace ProbabilityTheory
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → Set ι} {s u : Set ι} {i j : ι} {p q : I}
  {P : Measure Ω}

variable (u p) in
/-- The binomial distribution with parameter `p` on the set `u : Set V` is the measure on `Set V`
such that each element of `u` is taken with probability `p`, and the elements outside of `u` are
never taken. -/
noncomputable def bernoulliOn : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i ↦
    toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "Ber(" u ", " p ")" => bernoulliOn u p

instance : IsProbabilityMeasure Ber(u, p) :=
  MeasurableEquiv.setOf.symm.measurableEmbedding.isProbabilityMeasure_comap <| .of_forall fun P ↦
    ⟨{a | P a}, rfl⟩

variable (u p) in
lemma bernoulliOn_eq_map :
    Ber(u, p) = .map (fun p ↦ {i | p i})
      (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False) :=
  MeasurableEquiv.setOf.comap_symm

lemma bernoulliOn_apply (S : Set (Set ι)) :
    Ber(u, p) S = (infinitePi fun a ↦ toNNReal p • dirac (a ∈ u) + toNNReal (σ p) • dirac False)
      ((fun t a ↦ a ∈ t) '' S) := by
  convert MeasurableEquiv.setOf.symm.measurableEmbedding.comap_apply ..

lemma bernoulliOn_apply' (S : Set (Set ι)) :
    Ber(u, p) S = (infinitePi fun a ↦ toNNReal p • dirac (a ∈ u) + toNNReal (σ p) • dirac False)
      ((fun p ↦ {a | p a}) ⁻¹' S) := by
  convert MeasurableEquiv.setOf.symm.comap_apply ..

variable (u) in
@[simp] lemma bernoulliOn_zero : Ber(u, 0) = dirac ∅ := by simp [bernoulliOn_eq_map]

variable (u) in
@[simp] lemma bernoulliOn_one : Ber(u, 1) = dirac u := by simp [bernoulliOn_eq_map]

section Countable
variable [Countable ι]

-- TODO: Does this hold if `ι` isn't countable? Note: the current proof only needs `u` cocountable,
-- but we don't bother doing this minigeneralisation.
lemma bernoulliOn_ae_subset : ∀ᵐ s ∂Ber(u, p), s ⊆ u := by
  classical
  change _ = _
  simp only [Set.compl_setOf, Set.not_subset_iff_exists_mem_notMem, Set.setOf_exists, Set.setOf_and,
    measure_iUnion_null_iff]
  rintro a
  by_cases ha : a ∈ u
  · simp [*]
  calc
    Ber(u, p) ({s | a ∈ s} ∩ {s | a ∉ u})
    _ = Ber(u, p) {s | a ∈ s} := by simp [ha]
    _ = infinitePi (fun a ↦ toNNReal p • dirac (a ∈ u) + toNNReal (σ p) • dirac False)
            (cylinder {a} {fun _ ↦ True}) := by
      rw [bernoulliOn_apply']
      congr!
      ext
      simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder _ (.singleton _), ha]

end Countable

variable (u p) in
-- TODO: Generalise to countable `ι` and finite `u`. See the TODO on `infinitePi_pi`.
@[simp] lemma bernoulliOn_singleton [Finite ι] (hsu : s ⊆ u) :
    Ber(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  cases nonempty_fintype ι
  lift u to Finset ι using Set.toFinite _
  calc
    Ber(u, p) {s}
    _ = ∏ i, ((if i ∈ u ↔ i ∈ s then (toNNReal p : ENNReal) else 0) +
          if i ∈ s then 0 else (toNNReal (σ p) : ENNReal)) := by
      simp [bernoulliOn_apply, Set.image_singleton, Set.indicator]
      simp [ENNReal.smul_def]
    _ = ∏ i ∈ u, (if i ∈ s then (toNNReal p : ENNReal) else (toNNReal (σ p) : ENNReal)) := by
      rw [← Finset.prod_subset u.subset_univ (by
        simpa +contextual [ite_add_ite, ← ENNReal.coe_add] using fun _ ↦ mt (@hsu _))]
      simp +contextual [ite_add_ite]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.setOf_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_setOf, Set.diff_eq_compl_inter, Set.inter_comm]

/-! ### Bernoulli random variables -/

variable (X u p P) in
/-- A random variable `X : Ω → Set ι` is `p`-bernoulli on a set `u : Set ι` if its distribution is
the product over `u` of `p`-bernoulli random variables. -/
abbrev IsBernoulliOn : Prop := HasLaw X Ber(u, p) P

lemma isBernoulliOn_congr (hXY : X =ᵐ[P] Y) : IsBernoulliOn X u p P ↔ IsBernoulliOn Y u p P :=
  hasLaw_congr hXY

lemma IsBernoulliOn.identDistrib_mem (hX : IsBernoulliOn X u p P) (hi : i ∈ u) (hj : j ∈ u) :
    IdentDistrib (fun ω ↦ i ∈ X ω) (fun ω ↦ j ∈ X ω) P P where
  aemeasurable_fst := by fun_prop
  aemeasurable_snd := by fun_prop
  map_eq := sorry

lemma IsBernoulliOn.iIndepFun_mem (hX : IsBernoulliOn X u p P) :
    iIndepFun (fun i ω ↦ i ∈ X ω) P := sorry

lemma IsBernoulliOn.sdiff (hX : IsBernoulliOn X u p P) :
    IsBernoulliOn (fun ω ↦ u \ X ω) u (σ p) P where
  map_eq := sorry
  aemeasurable := sorry

lemma IsBernoulliOn.inter (hX : IsBernoulliOn X u p P) (hY : IsBernoulliOn Y u q P) :
    IsBernoulliOn (fun ω ↦ X ω ∩ Y ω) u (p * q) P where
  map_eq := sorry
  aemeasurable := sorry

variable [Countable ι]

lemma IsBernoulliOn.ae_subset (hX : IsBernoulliOn X u p P) : ∀ᵐ ω ∂P, X ω ⊆ u :=
  (hX.ae_iff sorry).2 bernoulliOn_ae_subset

lemma IsBernoulliOn.union (hX : IsBernoulliOn X u p P) (hY : IsBernoulliOn Y u q P) :
    IsBernoulliOn (fun ω ↦ X ω ∪ Y ω) u (σ <| σ p * σ q) P := by
  convert (hX.sdiff.inter hY.sdiff).sdiff using 0
  refine isBernoulliOn_congr ?_
  filter_upwards [hX.ae_subset, hY.ae_subset] with ω hXω hYω
  rw [Set.diff_inter, Set.diff_diff_cancel_left hXω, Set.diff_diff_cancel_left hYω]

end ProbabilityTheory
