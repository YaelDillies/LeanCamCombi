/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Density
import LeanCamCombi.Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Bollobás' graph containment lemma

This file proves Bollobás' lemma on graph containment.
-/

open Asymptotics Filter MeasureTheory
open scoped MeasureTheory  ENNReal NNReal SimpleGraph Topology unitInterval

namespace SimpleGraph
variable {V W Ω : Type*} [Fintype W] {G : ℕ → Ω → SimpleGraph V} (H : SimpleGraph W)
  [Fintype H.edgeSet] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ → I}
  (hG : ∀ n, IsBinomialRandom (G n) (p n) μ)

/-- **Bollobás' Graph Containment Lemma**, zero statement -/
lemma zero_statement
    (hp : (fun n ↦ p n : ℕ → ℝ) =o[atTop] (fun n ↦ n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ)) :
    Tendsto (fun n ↦ μ {ω | H ⊑ G n ω}) atTop (𝓝 0) :=
  sorry

/-- **Bollobás' Graph Containment Lemma**, one statement -/
lemma one_statement
    (hp : (fun n ↦ n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ) =o[atTop] (fun n ↦ p n : ℕ → ℝ)) :
    Tendsto (fun n ↦ μ {ω | H ⊑ G n ω}) atTop (𝓝 1) :=
  sorry

end SimpleGraph
