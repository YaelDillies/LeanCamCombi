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

variables (X Y : Ω → set α) {p q : ℝ≥0} [bernoulli_seq X p] [bernoulli_seq Y q]
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

variables [is_probability_measure (ℙ : measure Ω)]

protected lemma meas [fintype α] (s : finset α) :
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

instance compl : bernoulli_seq (λ ω, (X ω)ᶜ) (1 - p) :=
{ le_one := tsub_le_self,
  Indep_fun :=
  begin
    sorry
  end,
  map := sorry }

protected lemma inter (h : indep_fun X Y) : bernoulli_seq (λ ω, X ω ∩ Y ω) (p * q) :=
{ le_one := mul_le_one' (bernoulli_seq.le_one X) (bernoulli_seq.le_one Y),
  Indep_fun :=
  begin
    refine Indep_set.Indep_comap ((Indep_set_iff_measure_Inter_eq_prod $ λ i, _).2 _),
    refine measurable_set.inter _ _,
    sorry, -- needs refactor of `probability.independence`
    sorry, -- needs refactor of `probability.independence`
    refine λ s, _,
    -- We abused defeq using `Indep_set.Indep_comap`, so we fix it here
    change ℙ (⋂ i ∈ s, {ω | X ω i} ∩ {ω | Y ω i}) = s.prod (λ i, ℙ ({ω | X ω i} ∩ {ω | Y ω i})),
    simp_rw set.Inter_inter_distrib,
    rw [h, bernoulli_seq.Indep_fun X, bernoulli_seq.Indep_fun Y, ←finset.prod_mul_distrib],
    refine finset.prod_congr rfl (λ i hi, (h _ _ _ _).symm),
    sorry, -- needs refactor of `probability.independence`
    sorry, -- needs refactor of `probability.independence`
    sorry, -- needs refactor of `probability.independence`
    sorry, -- needs refactor of `probability.independence`
    sorry, -- needs refactor of `probability.independence`
    sorry, -- needs refactor of `probability.independence`
  end,
  map := begin
    rintro a,
    sorry
  end }

-- TODO: On a countable space, define one-to-one correspondance between `pmf` and probability
-- measures
-- extensionality lemma for `measure Prop`

protected lemma union (h : indep_fun X Y) : bernoulli_seq (λ ω, X ω ∪ Y ω) (p + q - p * q) :=
begin
  haveI := bernoulli_seq.inter (λ ω, (X ω)ᶜ) (λ ω, (Y ω)ᶜ) _,
  convert bernoulli_seq.compl (λ ω, (X ω)ᶜ ∩ (Y ω)ᶜ) using 1,
  ext : 1,
  simp only [set.compl_inter, compl_compl],
  sorry,
  sorry,
end

end bernoulli_seq
