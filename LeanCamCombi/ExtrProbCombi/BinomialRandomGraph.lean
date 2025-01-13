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

open MeasureTheory ProbabilityTheory
open scoped Finset ENNReal NNReal

variable {α Ω : Type*} [MeasurableSpace Ω]

/-- A graph-valued random variable is a `p`-binomial random graph (aka follows the Erdős–Rényi
model) if its edges are iid `p`-Bernoulli random variables. -/
abbrev IsBinomialRandomGraph (G : Ω → SimpleGraph α) (p : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop :=
  IsBernoulliSeq (fun ω ↦ (G ω).edgeSet) p μ

variable {G : Ω → SimpleGraph α} {H : SimpleGraph α} {p : ℝ≥0} (μ : Measure Ω)
  (hG : IsBinomialRandomGraph G p μ)

namespace IsBinomialRandomGraph
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

end IsBinomialRandomGraph
