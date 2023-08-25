/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Project.Mathlib.Combinatorics.SimpleGraph.Subgraph
import Project.WeightedCube

#align_import erdos_renyi.basic

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
  BernoulliSeq (fun ω => (G ω).edgeSetEmbedding) p μ

variable (G : Ω → SimpleGraph α) (H : SimpleGraph α) [∀ ω, DecidableRel (G ω).Adj] {p : ℝ≥0}
  (μ : Measure Ω) [IsProbabilityMeasure μ] [ErdosRenyi G p μ]

namespace ErdosRenyi

protected theorem le_one : p ≤ 1 :=
  BernoulliSeq.le_one (fun ω => (G ω).edgeSetEmbedding) μ

protected theorem iIndepFun : iIndepFun inferInstance (fun e ω => e ∈ (G ω).edgeSetEmbedding) μ :=
  BernoulliSeq.iIndepFun _ _

protected theorem map (e : Sym2 α) :
    Measure.map (fun ω => e ∈ (G ω).edgeSetEmbedding) μ =
      (Pmf.bernoulli' p <| ErdosRenyi.le_one G μ).toMeasure :=
  BernoulliSeq.map _ _ e

protected theorem aEMeasurable (e : Sym2 α) :
    AEMeasurable (fun ω => e ∈ (G ω).edgeSetEmbedding) μ :=
  BernoulliSeq.aEMeasurable _ _ e

protected theorem nullMeasurableSet (e : Sym2 α) :
    NullMeasurableSet {ω | e ∈ (G ω).edgeSetEmbedding} μ :=
  BernoulliSeq.nullMeasurableSet _ _ e

protected theorem identDistrib (d e : Sym2 α) :
    IdentDistrib (fun ω => d ∈ (G ω).edgeSetEmbedding) (fun ω => e ∈ (G ω).edgeSetEmbedding) μ μ :=
  BernoulliSeq.identDistrib _ _ d e

theorem meas_edge (e : Sym2 α) : μ {ω | e ∈ (G ω).edgeSetEmbedding} = p :=
  BernoulliSeq.meas_apply _ _ e

protected theorem meas [Fintype α] [DecidableEq α] [DecidableRel H.Adj] :
    μ {ω | G ω = H} =
      p ^ H.edgeFinset.card * (1 - p) ^ (Fintype.card (Sym2 α) - H.edgeFinset.card) :=
  by convert bernoulli_seq.meas (fun ω => (G ω).edgeSetEmbedding) μ H.edge_finset; ext; simp

end ErdosRenyi

