/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Subgraph
import LeanCamCombi.WeightedCube

/-!
# The Erdős–Rényi model

In this file, we define the Erdős–Rényi model through its marginals.
-/


open MeasureTheory ProbabilityTheory

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

variable {α Ω : Type _} [MeasurableSpace Ω]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
abbrev ErdosRenyi (G : Ω → SimpleGraph α) [∀ ω, DecidableRel (G ω).Adj] (p : ℝ≥0)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IsBernoulliSeq (fun ω ↦ (G ω).edgeSet) p μ

variable (G : Ω → SimpleGraph α) (H : SimpleGraph α) [∀ ω, DecidableRel (G ω).Adj] {p : ℝ≥0}
  (μ : Measure Ω) [IsProbabilityMeasure μ] [ErdosRenyi G p μ]

namespace ErdosRenyi

protected lemma le_one : p ≤ 1 :=
  IsBernoulliSeq.le_one (fun ω ↦ (G ω).edgeSet) μ

protected lemma iIndepFun : iIndepFun inferInstance (fun e ω ↦ e ∈ (G ω).edgeSet) μ :=
  IsBernoulliSeq.iIndepFun _ _

protected lemma map (e : Sym2 α) :
    Measure.map (fun ω ↦ e ∈ (G ω).edgeSet) μ =
      (Pmf.bernoulli' p $ ErdosRenyi.le_one G μ).toMeasure :=
  IsBernoulliSeq.map _ _ e

protected lemma aEMeasurable (e : Sym2 α) :
    AEMeasurable (fun ω ↦ e ∈ (G ω).edgeSet) μ :=
  IsBernoulliSeq.aEMeasurable _ _ e

protected lemma nullMeasurableSet (e : Sym2 α) :
    NullMeasurableSet {ω | e ∈ (G ω).edgeSet} μ :=
  IsBernoulliSeq.nullMeasurableSet _ _ e

protected lemma identDistrib (d e : Sym2 α) :
    IdentDistrib (fun ω ↦ d ∈ (G ω).edgeSet) (fun ω ↦ e ∈ (G ω).edgeSet) μ μ :=
  IsBernoulliSeq.identDistrib _ _ d e

lemma meas_edge (e : Sym2 α) : μ {ω | e ∈ (G ω).edgeSet} = p :=
  IsBernoulliSeq.meas_apply _ _ e

protected lemma meas [Fintype α] [DecidableEq α] [DecidableRel H.Adj] :
    μ {ω | G ω = H} =
      p ^ H.edgeFinset.card * (1 - p) ^ (Fintype.card (Sym2 α) - H.edgeFinset.card) := by convert bernoulli_seq.meas (fun ω ↦ (G ω).edgeSet) μ H.edge_finset; ext; simp

end ErdosRenyi
