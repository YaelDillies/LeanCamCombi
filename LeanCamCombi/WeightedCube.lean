/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Mathlib.Algebra.BigOperators.Basic
import LeanCamCombi.Mathlib.Pmf
import Mathlib.Probability.IdentDistrib
import LeanCamCombi.Mathlib.Probability.Independence

/-!
# Sequences of iid Bernoulli random variables

This file defines sequences of independent `p`-Bernoulli random variables and proves that the
complement of a sequence of independent Bernoulli random variables, union/intersection of two
independent sequences of independent Bernoulli random variables, are themselves sequences of
independent Bernoulli random variables.

## Main declarations

* `probability_theory.bernoulli_seq`: Typeclass for a sequence ``
-/


open MeasureTheory

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {α Ω : Type _} [MeasurableSpace Ω]

/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`le_one] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`iIndepFun] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`map] [] -/
/-- We say a `set α`-valued random is a sequence of iid Bernoulli random variables with parameter
`p` if `p ≤ 1`, the `a` projections (for `a : α`) are independent and are `p`-Bernoulli distributed.
-/
@[protect_proj]
class BernoulliSeq (X : Ω → Set α) (p : outParam ℝ≥0)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  le_one : p ≤ 1
  iIndepFun : iIndepFun inferInstance (fun a ω ↦ a ∈ X ω) μ
  map : ∀ a, Measure.map (fun ω ↦ a ∈ X ω) μ = (Pmf.bernoulli' p le_one).toMeasure

variable (X Y : Ω → Set α) (μ : Measure Ω) {p q : ℝ≥0} [BernoulliSeq X p μ] [BernoulliSeq Y q μ]

namespace BernoulliSeq

protected lemma ne_zero [Nonempty α] : μ ≠ 0 :=
  Nonempty.elim ‹_› fun a h ↦
    (Pmf.bernoulli' p $ BernoulliSeq.le_one X μ).toMeasure_ne_zero $ by
      rw [←bernoulli_seq.map X _ a, h, measure.map_zero]

protected lemma aEMeasurable (a : α) : AEMeasurable (fun ω ↦ a ∈ X ω) μ := by
  classical
  have : (Pmf.bernoulli' p $ bernoulli_seq.le_one X μ).toMeasure ≠ 0 := NeZero.ne _
  rw [←bernoulli_seq.map X _ a, measure.map] at this
  refine' (Ne.dite_ne_right_iff fun hX ↦ _).1 this
  rw [measure.mapₗ_ne_zero_iff hX.measurable_mk]
  haveI : Nonempty α := ⟨a⟩
  exact bernoulli_seq.ne_zero X _

@[simp]
protected lemma nullMeasurableSet (a : α) : NullMeasurableSet {ω | a ∈ X ω} μ := by
  rw [(by ext; simp : {ω | a ∈ X ω} = (fun ω ↦ a ∈ X ω) ⁻¹' {True})]
  exact
    (bernoulli_seq.aemeasurable X _ a).nullMeasurableSet_preimage MeasurableSpace.measurableSet_top

protected lemma identDistrib (a j : α) : IdentDistrib (fun ω ↦ a ∈ X ω) (fun ω ↦ X ω j) μ μ :=
  { aEMeasurable_fst := BernoulliSeq.aEMeasurable _ _ _
    aEMeasurable_snd := BernoulliSeq.aEMeasurable _ _ _
    map_eq := (BernoulliSeq.map _ _ _).trans (BernoulliSeq.map _ _ _).symm }

@[simp]
lemma meas_apply (a : α) : μ {ω | a ∈ X ω} = p := by
  rw [(_ : {ω | a ∈ X ω} = (fun ω ↦ a ∈ X ω) ⁻¹' {True}), ←
    measure.map_apply_of_aemeasurable (bernoulli_seq.aemeasurable X μ a)
      MeasurableSpace.measurableSet_top]
  · simp [bernoulli_seq.map X μ]
  · ext ω
    simp

variable [IsProbabilityMeasure (μ : Measure Ω)]

protected lemma meas [Fintype α] (s : Finset α) :
    μ {ω | {a | a ∈ X ω} = s} = p ^ s.card * (1 - p) ^ (Fintype.card α - s.card) := by
  classical
  simp_rw [Set.ext_iff, Set.setOf_forall]
  rw [(bernoulli_seq.Indep_fun X μ).meas_iInter, ←s.prod_mul_prod_compl, Finset.prod_eq_pow_card,
    Finset.prod_eq_pow_card, Finset.card_compl]
  · rintro a hi
    rw [Finset.mem_compl] at hi
    simp only [hi, ←Set.compl_setOf, null_measurable_set.prob_compl_eq_one_sub, Set.mem_setOf_eq,
      Finset.mem_coe, iff_false_iff, bernoulli_seq.null_measurable_set, meas_apply]
  · rintro a hi
    simp only [hi, Set.mem_setOf_eq, Finset.mem_coe, iff_true_iff, meas_apply]
  rintro a by_cases a ∈ s
  · simp only [*, Set.mem_setOf_eq, Finset.mem_coe, iff_true_iff]
    exact ⟨{True}, trivial, by ext; simp⟩
  · simp only [*, Set.mem_setOf_eq, Finset.mem_coe, iff_false_iff]
    exact ⟨{False}, trivial, by ext; simp⟩

/-- The complement of a sequence of independent `p`-Bernoulli random variables is a sequence of
independent `1 - p`-Bernoulli random variables. -/
instance compl : BernoulliSeq (fun ω ↦ X ωᶜ) (1 - p) μ where
  le_one := tsub_le_self
  iIndepFun := by
    simp only [Indep_fun, Set.mem_compl_iff, MeasurableSpace.comap_not]
    exact bernoulli_seq.Indep_fun X _
  map a := by
    have : Measurable Not := fun _ _ ↦ trivial
    simp only [Set.mem_compl_iff]
    rw [←this.aemeasurable.map_map_of_aemeasurable (bernoulli_seq.aemeasurable X μ _),
      bernoulli_seq.map, Pmf.map_toMeasure _ this, Pmf.map_not_bernoulli']

/-- The intersection of a sequence of independent `p`-Bernoulli and `q`-Bernoulli random variables
is a sequence of independent `p * q`-Bernoulli random variables. -/
protected lemma inter (h : IndepFun X Y μ) : BernoulliSeq (fun ω ↦ X ω ∩ Y ω) (p * q) μ :=
  { le_one := mul_le_one' (BernoulliSeq.le_one X μ) (BernoulliSeq.le_one Y μ)
    iIndepFun := by
      refine' Indep_set.Indep_comap ((Indep_set_iff_measure_Inter_eq_prod fun i ↦ _).2 _)
      refine' MeasurableSet.inter _ _
      sorry
      -- needs refactor of `probability.independence`
      sorry
      -- needs refactor of `probability.independence`
      refine' fun s ↦ _
      -- We abused defeq using `Indep_set.Indep_comap`, so we fix it here
      change μ (⋂ i ∈ s, {ω | X ω i} ∩ {ω | Y ω i}) = s.prod fun i ↦ μ ({ω | X ω i} ∩ {ω | Y ω i})
      simp_rw [Set.iInter_inter_distrib]
      rw [h, bernoulli_seq.Indep_fun X μ, bernoulli_seq.Indep_fun Y μ, ←Finset.prod_mul_distrib]
      refine' Finset.prod_congr rfl fun i hi ↦ (h _ _ _ _).symm
      sorry
      -- needs refactor of `probability.independence`
      sorry
      -- needs refactor of `probability.independence`
      sorry
      -- needs refactor of `probability.independence`
      sorry
      -- needs refactor of `probability.independence`
      sorry
      -- needs refactor of `probability.independence`
      sorry
    -- needs refactor of `probability.independence`
    map := by
      rintro a
      sorry }

/-- The union of a sequence of independent `p`-Bernoulli random variables is a sequence of
independent `1 - p`-Bernoulli random variables. -/
protected lemma union (h : IndepFun X Y μ) :
    BernoulliSeq (fun ω ↦ X ω ∪ Y ω) (p + q - p * q) μ := by
  haveI := bernoulli_seq.inter (fun ω ↦ X ωᶜ) (fun ω ↦ Y ωᶜ) μ _
  convert bernoulli_seq.compl (fun ω ↦ X ωᶜ ∩ Y ωᶜ) μ using 1
  simp only [Set.compl_inter, compl_compl]
  rw [mul_tsub, mul_one, tsub_tsub, tsub_tsub_cancel_of_le, tsub_mul, one_mul,
    add_tsub_assoc_of_le (mul_le_of_le_one_left' $ bernoulli_seq.le_one X μ)]
  ·
    exact
      (add_le_add_left (mul_le_of_le_one_right' $ bernoulli_seq.le_one Y μ) _).trans_eq
        (add_tsub_cancel_of_le $ bernoulli_seq.le_one X μ)
  rwa [indep_fun, MeasurableSpace.comap_compl, MeasurableSpace.comap_compl] <;>
    exact fun _ _ ↦ trivial

end BernoulliSeq

end ProbabilityTheory
