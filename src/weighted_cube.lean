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

variables {ι Ω : Type*} [measure_space Ω]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
@[protect_proj]
class bernoulli_seq (X : Ω → ι → Prop) (p : out_param ℝ≥0) : Prop :=
(le_one [] : p ≤ 1)
(Indep_fun [] : Indep_fun (λ _, infer_instance) (λ i ω, X ω i) ℙ)
(map [] : ∀ i, measure.map (λ ω, X ω i) ℙ = (pmf.bernoulli' p le_one).to_measure)

variables (X : Ω → ι → Prop) {p : ℝ≥0} [bernoulli_seq X p]
include X p

namespace bernoulli_seq

protected lemma ne_zero [nonempty ι] : (ℙ : measure Ω) ≠ 0 :=
nonempty.elim ‹_› $ λ i h, (pmf.bernoulli' p $ bernoulli_seq.le_one X).to_measure_ne_zero $
  by rw [←bernoulli_seq.map X i, h, measure.map_zero]

protected lemma ae_measurable (i : ι) : ae_measurable (λ ω, X ω i) :=
begin
  classical,
  have : (pmf.bernoulli' p $ bernoulli_seq.le_one X).to_measure ≠ 0 := ne_zero.ne _,
  rw [←bernoulli_seq.map X i, measure.map] at this,
  refine (ne.dite_ne_right_iff $ λ hX, _).1 this,
  rw measure.mapₗ_ne_zero_iff hX.measurable_mk,
  haveI : nonempty ι := ⟨i⟩,
  exact bernoulli_seq.ne_zero X,
end

@[simp]
protected lemma null_measurable_set (i : ι) : null_measurable_set {ω | X ω i} :=
begin
  rw [(by { ext, simp } : {ω | X ω i} = (λ ω, X ω i) ⁻¹' {true})],
  exact (bernoulli_seq.ae_measurable X i).null_measurable_set_preimage
    measurable_space.measurable_set_top
end

protected lemma ident_distrib (i j : ι) : ident_distrib (λ ω, X ω i) (λ ω, X ω j) :=
{ ae_measurable_fst := bernoulli_seq.ae_measurable _ _,
  ae_measurable_snd := bernoulli_seq.ae_measurable _ _,
  map_eq := (bernoulli_seq.map _ _).trans (bernoulli_seq.map _ _).symm }

@[simp] lemma meas_apply (i : ι) : ℙ {ω | X ω i} = p :=
begin
  rw [(_ : {ω | X ω i} = (λ ω, X ω i) ⁻¹' {true}),
    ← measure.map_apply_of_ae_measurable (bernoulli_seq.ae_measurable X i)
      measurable_space.measurable_set_top],
  { simp [bernoulli_seq.map X] },
  { ext ω, simp }
end

protected lemma meas [fintype ι] [is_probability_measure (ℙ : measure Ω)] (s : finset ι) :
  ℙ {ω | {i | X ω i} = s} = p ^ s.card * (1 - p) ^ (fintype.card ι - s.card) :=
begin
  classical,
  simp_rw [set.ext_iff, set.set_of_forall],
  rw [(bernoulli_seq.Indep_fun X).meas_Inter, ←s.prod_mul_prod_compl,
    finset.prod_eq_pow_card _ _ (p : ℝ≥0∞), finset.prod_eq_pow_card _ _ (1 - p : ℝ≥0∞),
    finset.card_compl],
  { rintro i hi,
    rw finset.mem_compl at hi,
    simp only [hi, ←set.compl_set_of, null_measurable_set.prob_compl_eq_one_sub, set.mem_set_of_eq,
      finset.mem_coe, iff_false, bernoulli_seq.null_measurable_set, meas_apply]},
  { rintro i hi,
    simp only [hi, set.mem_set_of_eq, finset.mem_coe, iff_true, meas_apply]},
  rintro i,
  by_cases i ∈ s,
  { simp only [*, set.mem_set_of_eq, finset.mem_coe, iff_true],
    exact ⟨{true}, trivial, by { ext, simp }⟩ },
  { simp only [*, set.mem_set_of_eq, finset.mem_coe, iff_false],
    exact ⟨{false}, trivial, by { ext, simp }⟩ }
end

end bernoulli_seq
