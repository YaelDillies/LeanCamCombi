/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import LeanCamCombi.ExtrProbCombi.BernoulliSeq

/-!
# Binomial random graphs

In this file, we define a predicate for binomial random graphs (aka the Erdős–Rényi model) through
its marginals.

Note that we do not prove here that such binomial random graphs always exist.

## Historical note

This is usually called the Erdős–Rényi model, but this name is historically inaccurate as Erdős and
Rényi introduced a closely related but different model. We therefore choose the name
"binomial random graph" to avoid confusion with this other model and because it is a more
descriptive name.
-/

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Finset ENNReal NNReal Set.Notation

variable {α Ω : Type*} [MeasurableSpace Ω]

/-- A graph-valued random variable is a `p`-binomial random graph (aka follows the Erdős–Rényi
model) if its edges are iid `p`-Bernoulli random variables. -/
abbrev IsBinomialRandomGraph (G : Ω → SimpleGraph α) (p : ℝ≥0) (μ : Measure Ω := by volume_tac) :
    Prop := IsBernoulliSeq (fun ω ↦ {e | ¬ e.IsDiag} ↓∩ (G ω).edgeSet) p μ

variable {G : Ω → SimpleGraph α} {H : SimpleGraph α} {p : ℝ≥0} (μ : Measure Ω)
  (hG : IsBinomialRandomGraph G p μ) {e e₁ e₂ : Sym2 α}

namespace IsBinomialRandomGraph
include hG

protected nonrec lemma le_one : p ≤ 1 := hG.le_one

lemma iIndepFun_mem_edgeSet_not_isDiag :
    iIndepFun inferInstance (fun (e : {e : Sym2 α // ¬ e.IsDiag}) ω ↦ ↑e ∈ (G ω).edgeSet) μ :=
  hG.iIndepFun

lemma iIndepFun_mem_edgeSet : iIndepFun inferInstance (fun e ω ↦ e ∈ (G ω).edgeSet) μ :=
  sorry

lemma map_mem_edgeSet (he : ¬ e.IsDiag) :
    Measure.map (fun ω ↦ e ∈ (G ω).edgeSet) μ = (PMF.bernoulli' p hG.le_one).toMeasure :=
  hG.map ⟨e, he⟩

lemma aemeasurable_mem_edgeSet : AEMeasurable (fun ω ↦ e ∈ (G ω).edgeSet) μ := by
  by_cases he : e.IsDiag
  · simp [imp_not_comm.1 (not_isDiag_of_mem_edgeSet _), he]
  · exact hG.aemeasurable ⟨e, he⟩

lemma nullMeasurableSet_mem_edgeSet (e : Sym2 α) : NullMeasurableSet {ω | e ∈ (G ω).edgeSet} μ := by
  by_cases he : e.IsDiag
  · simp [imp_not_comm.1 (not_isDiag_of_mem_edgeSet _), he]
  · exact hG.nullMeasurableSet ⟨e, he⟩

lemma identDistrib_mem_edgeSet_mem_edgeSet (he₁ : ¬ e₁.IsDiag) (he₂ : ¬ e₂.IsDiag) :
    IdentDistrib (fun ω ↦ e₁ ∈ (G ω).edgeSet) (fun ω ↦ e₂ ∈ (G ω).edgeSet) μ μ :=
  hG.identDistrib ⟨e₁, he₁⟩ ⟨e₂, he₂⟩

lemma meas_mem_edgeSet (he : ¬ e.IsDiag) : μ {ω | e ∈ (G ω).edgeSet} = p := hG.meas_apply ⟨e, he⟩

protected nonrec lemma meas [IsProbabilityMeasure μ] [Fintype α] [DecidableEq α]
    [DecidableRel H.Adj] :
    μ {ω | G ω = H} =
      p ^ #H.edgeFinset * (1 - p) ^ (Fintype.card {e : Sym2 α // ¬ e.IsDiag} - #H.edgeFinset) := by
  have := hG.meas
    (H.edgeFinset.attach.map <| ⟨Set.inclusion fun e he ↦
      not_isDiag_of_mem_edgeSet _ <| mem_edgeFinset.1 he, Set.inclusion_injective _⟩)
  simp at this
  rw [Finset.card_attach, ← Fintype.card_subtype_compl] at this
  convert this
  sorry

end IsBinomialRandomGraph
