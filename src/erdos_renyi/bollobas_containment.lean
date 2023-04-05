/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.asymptotics.asymptotics
import mathlib.combinatorics.simple_graph.containment
import mathlib.combinatorics.simple_graph.density
import erdos_renyi.basic

/-!
# Bollobás' graph containment lemma

This file proves Bollobás' lemma on graph containment.
-/

open asymptotics filter measure_theory probability_theory
open_locale measure_theory probability_theory ennreal nnreal topological_space

variables {α β Ω : Type*} [fintype β] (G : ℕ → Ω → simple_graph α) (H : simple_graph β)
  [fintype H.edge_set] [Π n ω, decidable_rel (G n ω).adj] [measurable_space Ω] (μ : measure Ω)
  [is_probability_measure μ] {p : ℕ → ℝ≥0} [∀ n, erdos_renyi (G n) (p n) μ]

namespace simple_graph

/-- **Bollobás' Graph Containment Lemma, zero statement** -/
lemma zero_statement
  (hp : (λ n, p n : ℕ → ℝ) =o[at_top] (λ n, n ^ (- H.max_edge_subdensity⁻¹ : ℝ) : ℕ → ℝ)) :
  tendsto (λ n, μ {ω | H ⊑ G n ω}) at_top (𝓝 0) := sorry

/-- **Bollobás' Graph Containment Lemma, one statement** -/
lemma one_statement
  (hp : (λ n, n ^ (- H.max_edge_subdensity⁻¹ : ℝ) : ℕ → ℝ) =o[at_top] (λ n, p n : ℕ → ℝ)) :
  tendsto (λ n, μ {ω | H ⊑ G n ω}) at_top (𝓝 1) := sorry

end simple_graph
