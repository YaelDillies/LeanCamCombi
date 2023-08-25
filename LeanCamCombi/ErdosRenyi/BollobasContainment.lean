/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Analysis.Asymptotics.Asymptotics
import Project.Mathlib.Combinatorics.SimpleGraph.Containment
import Project.Mathlib.Combinatorics.SimpleGraph.Density
import Project.ErdosRenyi.Basic

#align_import erdos_renyi.bollobas_containment

/-!
# Bollobás' graph containment lemma

This file proves Bollobás' lemma on graph containment.
-/


open Asymptotics Filter MeasureTheory ProbabilityTheory

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal SimpleGraph Topology

variable {α β Ω : Type _} [Fintype β] (G : ℕ → Ω → SimpleGraph α) (H : SimpleGraph β)
  [Fintype H.edgeSetEmbedding] [∀ n ω, DecidableRel (G n ω).Adj] [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] {p : ℕ → ℝ≥0} [∀ n, ErdosRenyi (G n) (p n) μ]

namespace SimpleGraph

/-- **Bollobás' Graph Containment Lemma, zero statement** -/
theorem zero_statement
    (hp : (fun n => p n : ℕ → ℝ) =o[atTop] (fun n => n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ)) :
    Tendsto (fun n => μ {ω | H ⊑ G n ω}) atTop (𝓝 0) :=
  sorry

/-- **Bollobás' Graph Containment Lemma, one statement** -/
theorem one_statement
    (hp : (fun n => n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ) =o[atTop] (fun n => p n : ℕ → ℝ)) :
    Tendsto (fun n => μ {ω | H ⊑ G n ω}) atTop (𝓝 1) :=
  sorry

end SimpleGraph

