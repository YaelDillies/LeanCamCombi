/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import mathlib.big_ops
import mathlib.independence
import mathlib.measure
import mathlib.pmf
import probability.ident_distrib

/-!
We want to formulate a sequence of iid Bernoulli random variables
-/

open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal nnreal

variables {α Ω : Type*} [measure_space Ω]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
@[protect_proj]
class bernoulli_seq (X : Ω → set α) (p : out_param ℝ≥0) : Prop :=
(le_one [] : p ≤ 1)
(Indep_fun [] : Indep_fun infer_instance (λ a ω, a ∈ X ω) ℙ)
(map [] : ∀ a, measure.map (λ ω, a ∈ X ω) ℙ = (pmf.bernoulli' p le_one).to_measure)

variables (X : Ω → set α) {p : ℝ≥0} [bernoulli_seq X p]
include X p

namespace bernoulli_seq

protected lemma ne_zero [nonempty α] : (ℙ : measure Ω) ≠ 0 :=
nonempty.elim ‹_› $ λ a h, (pmf.bernoulli' p $ bernoulli_seq.le_one X).to_measure_ne_zero $
  by rw [←bernoulli_seq.map X a, h, measure.map_zero]

protected lemma ae_measurable (a : α) : ae_measurable (λ ω, a ∈ X ω) :=
begin
  classical,
  have : (pmf.bernoulli' p $ bernoulli_seq.le_one X).to_measure ≠ 0 := ne_zero.ne _,
  rw [←bernoulli_seq.map X a, measure.map] at this,
  refine (ne.dite_ne_right_iff $ λ hX, _).1 this,
  rw measure.mapₗ_ne_zero_iff hX.measurable_mk,
  haveI : nonempty α := ⟨a⟩,
  exact bernoulli_seq.ne_zero X,
end

@[simp]
protected lemma null_measurable_set (a : α) : null_measurable_set {ω | a ∈ X ω} :=
begin
  rw [(by { ext, simp } : {ω | a ∈ X ω} = (λ ω, a ∈ X ω) ⁻¹' {true})],
  exact (bernoulli_seq.ae_measurable X a).null_measurable_set_preimage
    measurable_space.measurable_set_top
end

protected lemma ident_distrib (a j : α) : ident_distrib (λ ω, a ∈ X ω) (λ ω, X ω j) :=
{ ae_measurable_fst := bernoulli_seq.ae_measurable _ _,
  ae_measurable_snd := bernoulli_seq.ae_measurable _ _,
  map_eq := (bernoulli_seq.map _ _).trans (bernoulli_seq.map _ _).symm }

@[simp] lemma meas_apply (a : α) : ℙ {ω | a ∈ X ω} = p :=
begin
  rw [(_ : {ω | a ∈ X ω} = (λ ω, a ∈ X ω) ⁻¹' {true}),
    ← measure.map_apply_of_ae_measurable (bernoulli_seq.ae_measurable X a)
      measurable_space.measurable_set_top],
  { simp [bernoulli_seq.map X] },
  { ext ω, simp }
end

protected lemma meas [fintype α] [is_probability_measure (ℙ : measure Ω)] (s : finset α) :
  ℙ {ω | {a | a ∈ X ω} = s} = p ^ s.card * (1 - p) ^ (fintype.card α - s.card) :=
begin
  classical,
  simp_rw [set.ext_iff, set.set_of_forall],
  rw [(bernoulli_seq.Indep_fun X).meas_Inter, ←s.prod_mul_prod_compl,
    finset.prod_eq_pow_card _ _ (p : ℝ≥0∞), finset.prod_eq_pow_card _ _ (1 - p : ℝ≥0∞),
    finset.card_compl],
  { rintro a hi,
    rw finset.mem_compl at hi,
    simp only [hi, ←set.compl_set_of, null_measurable_set.prob_compl_eq_one_sub, set.mem_set_of_eq,
      finset.mem_coe, iff_false, bernoulli_seq.null_measurable_set, meas_apply]},
  { rintro a hi,
    simp only [hi, set.mem_set_of_eq, finset.mem_coe, iff_true, meas_apply]},
  rintro a,
  by_cases a ∈ s,
  { simp only [*, set.mem_set_of_eq, finset.mem_coe, iff_true],
    exact ⟨{true}, trivial, by { ext, simp }⟩ },
  { simp only [*, set.mem_set_of_eq, finset.mem_coe, iff_false],
    exact ⟨{false}, trivial, by { ext, simp }⟩ }
end

end bernoulli_seq
