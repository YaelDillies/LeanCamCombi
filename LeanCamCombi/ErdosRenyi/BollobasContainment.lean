/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Containment
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Density
import LeanCamCombi.ErdosRenyi.Basic

/-!
# Bollobás' graph containment lemma

This file proves Bollobás' lemma on graph containment.
-/


open Asymptotics Filter MeasureTheory ProbabilityTheory

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal SimpleGraph Topology

variable {α β Ω : Type*} [Fintype β] {G : ℕ → Ω → SimpleGraph α} (H : SimpleGraph β)
  [Fintype H.edgeSet] [∀ n ω, DecidableRel (G n ω).Adj] [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] {p : ℕ → ℝ≥0} (hG : ∀ n, ErdosRenyi (G n) (p n) μ)

namespace SimpleGraph

/-- **Bollobás' Graph Containment Lemma, zero statement** -/
lemma zero_statement
    (hp : (fun n ↦ p n : ℕ → ℝ) =o[atTop] (fun n ↦ n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ)) :
    Tendsto (fun n ↦ μ {ω | H ⊑ G n ω}) atTop (𝓝 0) :=
  sorry

/-- **Bollobás' Graph Containment Lemma, one statement** -/
lemma one_statement
    (hp : (fun n ↦ n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ) =o[atTop] (fun n ↦ p n : ℕ → ℝ)) :
    Tendsto (fun n ↦ μ {ω | H ⊑ G n ω}) atTop (𝓝 1) :=
  sorry

end SimpleGraph
