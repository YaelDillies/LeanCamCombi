/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.ident_distrib
import probability.probability_mass_function.constructions

/-
We want to formlate a sequence of iid Bernoulli random variables
-/

open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal nnreal

variables {ι Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

section mathlib

@[simp]
lemma measure.map_eq_zero_iff {α β : Type*} [measurable_space α] [measurable_space β]
  {μ : measure α} {f : α → β} (hf : ae_measurable f μ) :
  μ.map f = 0 ↔ μ = 0 :=
begin
  split,
  { intro h,
    replace h := congr_fun (congr_arg coe_fn h) set.univ,
    rwa [measure.map_apply_of_ae_measurable hf measurable_set.univ, set.preimage_univ, 
      measure.coe_zero, pi.zero_apply, measure.measure_univ_eq_zero] at h },
  { rintro rfl,
    exact measure.map_zero _ }
end

@[simp]
lemma measure.mapₗ_eq_zero_iff {α β : Type*} [measurable_space α] [measurable_space β]
  {μ : measure α} {f : α → β} (hf : measurable f) :
  measure.mapₗ f μ = 0 ↔ μ = 0 :=
begin
  classical,
  rw [← measure.map_eq_zero_iff hf.ae_measurable, measure.map, dif_pos hf.ae_measurable,
    measure.mapₗ_congr hf hf.ae_measurable.measurable_mk],
  refine hf.ae_measurable.ae_eq_mk
end

end mathlib

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
def bernoulli_seq (X : Ω → ι → bool) (p : ℝ≥0) : Prop := 
Indep_fun (λ _, infer_instance) (λ i ω, X ω i) ℙ ∧ 
∀ i, measure.map (λ ω, X ω i) ℙ = (pmf.bernoulli (min p 1) $ min_le_right _ _).to_measure

variables {X : Ω → ι → bool} {p : ℝ≥0}

namespace bernoulli_seq

def bool.measurable_space : measurable_space bool := ⊤

local attribute [instance] bool.measurable_space

@[protected]
lemma Indep_fun (h : bernoulli_seq X p) : 
  Indep_fun (λ _, infer_instance) (λ i ω, X ω i) ℙ := 
h.1

@[protected]
lemma map (h : bernoulli_seq X p) (i : ι) : measure.map (λ ω, X ω i) ℙ = 
  (pmf.bernoulli (min p 1) $ min_le_right _ _).to_measure := h.2 i

@[protected]
lemma ae_measurable (h : bernoulli_seq X p) (i : ι) : ae_measurable (λ ω, X ω i) :=
begin
  classical,
  suffices : (pmf.bernoulli (min p 1) $ min_le_right _ _).to_measure ≠ 0,
  { rw [← h.map i, measure.map] at this,
    refine (ne.dite_ne_right_iff $ λ hX hzero, _).1 this,
    rw measure.mapₗ_eq_zero_iff hX.measurable_mk at hzero,
    exact is_probability_measure.ne_zero ℙ hzero },
  exact is_probability_measure.ne_zero _
end

@[protected]
lemma ident_distrib (h : bernoulli_seq X p) (i j : ι) : 
  ident_distrib (λ ω, X ω i) (λ ω, X ω j) :=
{ ae_measurable_fst := h.ae_measurable i,
  ae_measurable_snd := h.ae_measurable j,
  map_eq := (h.map i).trans (h.map j).symm }

end bernoulli_seq