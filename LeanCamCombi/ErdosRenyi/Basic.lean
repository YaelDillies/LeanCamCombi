/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import LeanCamCombi.BernoulliSeq

/-!
# The Erdős–Rényi model

In this file, we define the Erdős–Rényi model through its marginals.
-/

open MeasureTheory ProbabilityTheory
open scoped Finset ENNReal NNReal

variable {α Ω : Type*} [MeasurableSpace Ω]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
abbrev ErdosRenyi (G : Ω → SimpleGraph α) (p : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop :=
  IsBernoulliSeq (fun ω ↦ (G ω).edgeSet) p μ

variable {G : Ω → SimpleGraph α} {H : SimpleGraph α} {p : ℝ≥0} (μ : Measure Ω)
  (hG : ErdosRenyi G p μ)

namespace ErdosRenyi
include hG

protected nonrec lemma le_one : p ≤ 1 := hG.le_one

protected nonrec lemma iIndepFun : iIndepFun inferInstance (fun e ω ↦ e ∈ (G ω).edgeSet) μ :=
  hG.iIndepFun

protected nonrec lemma map (e : Sym2 α) :
    Measure.map (fun ω ↦ e ∈ (G ω).edgeSet) μ = (PMF.bernoulli' p hG.le_one).toMeasure :=
  hG.map _

protected nonrec lemma aemeasurable (e : Sym2 α) : AEMeasurable (fun ω ↦ e ∈ (G ω).edgeSet) μ :=
  hG.aemeasurable _

protected nonrec lemma nullMeasurableSet (e : Sym2 α) :
    NullMeasurableSet {ω | e ∈ (G ω).edgeSet} μ := hG.nullMeasurableSet _

protected nonrec lemma identDistrib (d e : Sym2 α) :
    IdentDistrib (fun ω ↦ d ∈ (G ω).edgeSet) (fun ω ↦ e ∈ (G ω).edgeSet) μ μ :=
  hG.identDistrib _ _

lemma meas_edge (e : Sym2 α) : μ {ω | e ∈ (G ω).edgeSet} = p := hG.meas_apply _

protected nonrec lemma meas [IsProbabilityMeasure μ] [Fintype α] [DecidableEq α]
    [DecidableRel H.Adj] :
    μ {ω | G ω = H} =
      p ^ #H.edgeFinset * (1 - p) ^ (Fintype.card (Sym2 α) - #H.edgeFinset) := by
  simpa using hG.meas H.edgeFinset

end ErdosRenyi
