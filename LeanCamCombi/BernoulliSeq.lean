/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Mathlib.Probability.IdentDistrib
import LeanCamCombi.Mathlib.Probability.Independence.Basic
import LeanCamCombi.Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Sequences of iid Bernoulli random variables

This file defines sequences of independent `p`-Bernoulli random variables and proves that the
complement of a sequence of independent Bernoulli random variables, union/intersection of two
independent sequences of independent Bernoulli random variables, are themselves sequences of
independent Bernoulli random variables.

## Main declarations

* `ProbabilityTheory.IsBernoulliSeq`: Typeclass for a sequence of iid Bernoulli random variables
  with parameter `p`
-/

open Fintype MeasureTheory Set
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory
variable {α Ω : Type*} [MeasurableSpace Ω]

/-- We say a `set α`-valued random is a sequence of iid Bernoulli random variables with parameter
`p` if `p ≤ 1`, the `a` projections (for `a : α`) are independent and are `p`-Bernoulli distributed.
-/
structure IsBernoulliSeq (X : Ω → Set α) (p : outParam ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop
    where
  protected le_one : p ≤ 1
  protected iIndepFun : iIndepFun inferInstance (fun a ω ↦ a ∈ X ω) μ
  protected map : ∀ a, Measure.map (fun ω ↦ a ∈ X ω) μ = (PMF.bernoulli' p le_one).toMeasure

variable {X Y : Ω → Set α} {μ : Measure Ω} {p q : ℝ≥0} (hX : IsBernoulliSeq X p μ)
  (hY : IsBernoulliSeq Y q μ)

namespace IsBernoulliSeq

include hX

protected lemma ne_zero [Nonempty α] : μ ≠ 0 :=
  Nonempty.elim ‹_› fun a h ↦ (PMF.bernoulli' p hX.le_one).toMeasure_ne_zero $ by
    rw [← hX.map a, h, Measure.map_zero]

protected lemma aemeasurable (a : α) : AEMeasurable (fun ω ↦ a ∈ X ω) μ := by
  classical
  have : (PMF.bernoulli' p hX.le_one).toMeasure ≠ 0 := NeZero.ne _
  rw [← hX.map a, Measure.map] at this
  refine (Ne.dite_ne_right_iff fun hX' ↦ ?_).1 this
  rw [Measure.mapₗ_ne_zero_iff hX'.measurable_mk]
  haveI : Nonempty α := ⟨a⟩
  exact hX.ne_zero

@[simp] protected lemma nullMeasurableSet (a : α) : NullMeasurableSet {ω | a ∈ X ω} μ := by
  rw [(by ext; simp : {ω | a ∈ X ω} = (fun ω ↦ a ∈ X ω) ⁻¹' {True})]
  exact (hX.aemeasurable a).nullMeasurableSet_preimage MeasurableSpace.measurableSet_top

protected lemma identDistrib (a j : α) : IdentDistrib (fun ω ↦ a ∈ X ω) (fun ω ↦ X ω j) μ μ :=
  { aemeasurable_fst := hX.aemeasurable _
    aemeasurable_snd := hX.aemeasurable _
    map_eq := (hX.map _).trans (hX.map _).symm }

@[simp] lemma meas_apply (a : α) : μ {ω | a ∈ X ω} = p := by
  rw [(_ : {ω | a ∈ X ω} = (fun ω ↦ a ∈ X ω) ⁻¹' {True}),
    ← Measure.map_apply_of_aemeasurable (hX.aemeasurable a) MeasurableSpace.measurableSet_top]
  · simp [hX.map]
  · ext ω
    simp

protected lemma meas [IsProbabilityMeasure (μ : Measure Ω)] [Fintype α] (s : Finset α) :
    μ {ω | {a | a ∈ X ω} = s} = (p : ℝ≥0∞) ^ s.card * (1 - p : ℝ≥0∞) ^ (card α - s.card) := by
  classical
  simp_rw [Set.ext_iff, setOf_forall]
  rw [hX.iIndepFun.meas_iInter, ← s.prod_mul_prod_compl, Finset.prod_eq_pow_card,
    Finset.prod_eq_pow_card, Finset.card_compl]
  · rintro a hi
    rw [Finset.mem_compl] at hi
    simp only [hi, ← compl_setOf, prob_compl_eq_one_sub₀, mem_setOf_eq, Finset.mem_coe,
      iff_false_iff, hX.nullMeasurableSet, hX.meas_apply]
  · rintro a hi
    simp only [hi, mem_setOf_eq, Finset.mem_coe, iff_true_iff, hX.meas_apply]
  rintro a
  by_cases a ∈ s
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_true_iff, *]
    exact ⟨{True}, trivial, by ext; simp⟩
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_false_iff, *]
    exact ⟨{False}, trivial, by ext; simp⟩

/-- The complement of a sequence of independent `p`-Bernoulli random variables is a sequence of
independent `1 - p`-Bernoulli random variables. -/
lemma compl : IsBernoulliSeq (fun ω ↦ (X ω)ᶜ) (1 - p) μ where
  le_one := tsub_le_self
  iIndepFun := by
    simp only [iIndepFun_iff, mem_compl_iff, MeasurableSpace.comap_not]
    exact (iIndepFun_iff _ _ _).1 hX.iIndepFun
  map a := by
    have : Measurable Not := fun _ _ ↦ trivial
    refine (this.aemeasurable.map_map_of_aemeasurable (hX.aemeasurable _)).symm.trans ?_
    rw [hX.map, PMF.map_toMeasure _ this, PMF.map_not_bernoulli']

variable [IsProbabilityMeasure (μ : Measure Ω)]

include hY

/-- The intersection of a sequence of independent `p`-Bernoulli and `q`-Bernoulli random variables
is a sequence of independent `p * q`-Bernoulli random variables. -/
protected lemma inter (h : IndepFun X Y μ) : IsBernoulliSeq (fun ω ↦ X ω ∩ Y ω) (p * q) μ where
  le_one := mul_le_one' hX.le_one hY.le_one
  iIndepFun := by
    refine iIndepSet.Indep_comap ((iIndepSet_iff_meas_iInter fun i ↦ ?_).2 ?_)
    refine MeasurableSet.inter ?_ ?_
    sorry -- needs refactor of `Probability.Independence.Basic`
    sorry -- needs refactor of `Probability.Independence.Basic`
    refine fun s ↦ ?_
    -- We abused defeq using `iIndepSet.Indep_comap`, so we fix it here
    change μ (⋂ i ∈ s, {ω | X ω i} ∩ {ω | Y ω i}) = s.prod fun i ↦ μ ({ω | X ω i} ∩ {ω | Y ω i})
    simp_rw [iInter_inter_distrib]
    rw [h.meas_inter, hX.iIndepFun.meas_biInter, hY.iIndepFun.meas_biInter,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi ↦ (h.meas_inter ?_ ?_).symm
    sorry -- needs refactor of `Probability.Independence.Basic`
    sorry -- needs refactor of `Probability.Independence.Basic`
    sorry -- needs refactor of `Probability.Independence.Basic`
    sorry -- needs refactor of `Probability.Independence.Basic`
    sorry -- needs refactor of `Probability.Independence.Basic`
    sorry -- needs refactor of `Probability.Independence.Basic`
  map a := sorry

/-- The union of a sequence of independent `p`-Bernoulli random variables and `q`-Bernoulli random
variables is a sequence of independent `p + q - p * q`-Bernoulli random variables. -/
protected lemma union (h : IndepFun X Y μ) :
    IsBernoulliSeq (fun ω ↦ X ω ∪ Y ω) (p + q - p * q) μ := by
  convert (hX.compl.inter hY.compl _).compl using 1
  · simp [compl_inter]
  · rw [mul_tsub, mul_one, tsub_tsub, tsub_tsub_cancel_of_le, tsub_mul, one_mul,
      add_tsub_assoc_of_le (mul_le_of_le_one_left' $ hX.le_one)]
    · exact (add_le_add_left (mul_le_of_le_one_right' $ hY.le_one) _).trans_eq
        (add_tsub_cancel_of_le hX.le_one)
  · rwa [IndepFun_iff, MeasurableSpace.comap_compl measurable_compl,
      MeasurableSpace.comap_compl measurable_compl, ← IndepFun_iff]

end IsBernoulliSeq
end ProbabilityTheory
