/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import combinatorics.simple_graph.basic
import weighted_cube

/-!
# The Erdős–Rényi model

In this file, we define the Erdős–Rényi model through its marginals.
-/

open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal nnreal

variables {α Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
def erdos_renyi (G : Ω → simple_graph α) [Π ω, decidable_rel ((G ω).adj)] (p : ℝ≥0) : Prop :=
bernoulli_seq (λ ω e, e ∈ (G ω).edge_set) p

variables {G : Ω → simple_graph α} [Π ω, decidable_rel ((G ω).adj)] {p : ℝ≥0}

namespace erdos_renyi

@[protected]
lemma Indep_fun (h : erdos_renyi G p) :
  Indep_fun (λ _, infer_instance) (λ e ω, (e ∈ (G ω).edge_set : bool)) ℙ := h.1

@[protected]
lemma map (h : erdos_renyi G p) (e : sym2 α) :
  measure.map (λ ω, (e ∈ (G ω).edge_set : bool)) ℙ
    = (pmf.bernoulli (min p 1) $ min_le_right _ _).to_measure := h.2 _

@[protected]
lemma ae_measurable [ne_zero (ℙ : measure Ω)] (h : erdos_renyi G p) (e : sym2 α) :
  ae_measurable (λ ω, (e ∈ (G ω).edge_set : bool)) :=
h.ae_measurable _

@[protected]
lemma ident_distrib [ne_zero (ℙ : measure Ω)] (h : erdos_renyi G p) (d e : sym2 α) :
  ident_distrib (λ ω, (d ∈ (G ω).edge_set : bool)) (λ ω, (e ∈ (G ω).edge_set : bool)) :=
h.ident_distrib _ _

lemma meas_edge_mem_eq [ne_zero (ℙ : measure Ω)] (h : erdos_renyi G p) (e : sym2 α) :
  ℙ {ω | e ∈ (G ω).edge_set} = min p 1 :=
begin
  rw [(_ : {ω | e ∈ (G ω).edge_set} = (λ ω, (e ∈ (G ω).edge_set : bool)) ⁻¹' {tt}),
    ← measure.map_apply_of_ae_measurable (h.ae_measurable e) measurable_space.measurable_set_top],
  { simp [h.map] },
  { ext ω,
    simp }
end

end erdos_renyi
