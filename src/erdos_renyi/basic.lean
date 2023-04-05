/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import mathlib.combinatorics.simple_graph.subgraph
import weighted_cube

/-!
# The Erdős–Rényi model

In this file, we define the Erdős–Rényi model through its marginals.
-/

open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal nnreal

variables {α Ω : Type*} [measurable_space Ω]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
abbreviation erdos_renyi (G : Ω → simple_graph α) [Π ω, decidable_rel (G ω).adj] (p : ℝ≥0)
  (μ : measure Ω . volume_tac) : Prop :=
bernoulli_seq (λ ω, (G ω).edge_set) p μ

variables (G : Ω → simple_graph α) (H : simple_graph α) [Π ω, decidable_rel (G ω).adj] {p : ℝ≥0}
  (μ : measure Ω) [is_probability_measure μ] [erdos_renyi G p μ]
include G p

namespace erdos_renyi

protected lemma le_one : p ≤ 1 := bernoulli_seq.le_one (λ ω, (G ω).edge_set) μ

protected lemma Indep_fun : Indep_fun infer_instance (λ e ω, e ∈ (G ω).edge_set) μ :=
bernoulli_seq.Indep_fun _ _

protected lemma map (e : sym2 α) :
  measure.map (λ ω, e ∈ (G ω).edge_set) μ =
    (pmf.bernoulli' p $ erdos_renyi.le_one G μ).to_measure :=
bernoulli_seq.map _ _ e

protected lemma ae_measurable (e : sym2 α) : ae_measurable (λ ω, e ∈ (G ω).edge_set) μ :=
bernoulli_seq.ae_measurable _ _ e

protected lemma null_measurable_set (e : sym2 α) : null_measurable_set {ω | e ∈ (G ω).edge_set} μ :=
bernoulli_seq.null_measurable_set _ _ e

protected lemma ident_distrib (d e : sym2 α) :
  ident_distrib (λ ω, d ∈ (G ω).edge_set) (λ ω, e ∈ (G ω).edge_set) μ μ :=
bernoulli_seq.ident_distrib _ _ d e

lemma meas_edge (e : sym2 α) : μ {ω | e ∈ (G ω).edge_set} = p :=
bernoulli_seq.meas_apply _ _ e

protected lemma meas [fintype α] [decidable_eq α] [decidable_rel H.adj] :
  μ {ω | G ω = H}
    = p ^ H.edge_finset.card * (1 - p) ^ (fintype.card (sym2 α) - H.edge_finset.card) :=
by { convert bernoulli_seq.meas (λ ω, (G ω).edge_set) μ H.edge_finset, ext, simp }

end erdos_renyi
