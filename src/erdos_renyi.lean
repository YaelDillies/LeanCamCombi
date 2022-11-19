/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import combinatorics.simple_graph.basic
import mathlib.simple_graph
import weighted_cube

/-!
# The Erdős–Rényi model

In this file, we define the Erdős–Rényi model through its marginals.
-/

open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal nnreal

variables {α Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
abbreviation erdos_renyi (G : Ω → simple_graph α) [Π ω, decidable_rel ((G ω).adj)] : ℝ≥0 → Prop :=
bernoulli_seq $ λ ω e, e ∈ (G ω).edge_set

variables (G : Ω → simple_graph α) (H : simple_graph α) [Π ω, decidable_rel ((G ω).adj)] {p : ℝ≥0}
  [erdos_renyi G p]
include G p

namespace erdos_renyi

protected lemma le_one : p ≤ 1 := bernoulli_seq.le_one (λ ω e, e ∈ (G ω).edge_set)

protected lemma Indep_fun : Indep_fun (λ _, infer_instance) (λ e ω, e ∈ (G ω).edge_set) :=
bernoulli_seq.Indep_fun _

protected lemma map (e : sym2 α) :
  measure.map (λ ω, (e ∈ (G ω).edge_set : Prop)) ℙ
    = (pmf.bernoulli' p $ erdos_renyi.le_one G).to_measure :=
bernoulli_seq.map _ e

protected lemma ae_measurable (e : sym2 α) : ae_measurable (λ ω, e ∈ (G ω).edge_set) :=
bernoulli_seq.ae_measurable _ e

protected lemma ident_distrib (d e : sym2 α) :
  ident_distrib (λ ω, (d ∈ (G ω).edge_set : Prop)) (λ ω, e ∈ (G ω).edge_set) :=
bernoulli_seq.ident_distrib _ d e

lemma meas_edge (e : sym2 α) : ℙ {ω | e ∈ (G ω).edge_set} = p :=
bernoulli_seq.meas_apply _ e

protected lemma meas [fintype α] [decidable_eq α] [decidable_rel H.adj] :
  ℙ {ω | G ω = H}
    = p ^ H.edge_finset.card * (1 - p) ^ (fintype.card (sym2 α) - H.edge_finset.card) :=
by { convert bernoulli_seq.meas (λ ω e, e ∈ (G ω).edge_set) H.edge_finset, ext, simp }

end erdos_renyi
