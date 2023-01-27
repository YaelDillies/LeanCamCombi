import mathlib.measure_theory.measure.measure_space
import probability.independence

open measure_theory measurable_space set
open_locale big_operators

namespace probability_theory
variables {Ω ι : Type*} [measurable_space Ω] {π : ι → set (set Ω)} {μ : measure Ω}

lemma Indep_sets.meas_Inter [fintype ι] (h : Indep_sets π μ) {f : ι → set Ω} (hf : ∀ i, f i ∈ π i) :
  μ (⋂ i, f i) = ∏ i, μ (f i) :=
by simp [← h _ (λ i _, hf _)]

lemma Indep_comap_iff {s : ι → set Ω} :
  Indep (λ i, measurable_space.comap (∈ s i) ⊤) μ ↔ Indep_set s μ :=
by { simp_rw ←generate_from_singleton, refl }

alias Indep_comap_iff ↔ _ Indep_set.Indep_comap

lemma Indep_sets_singleton_iff {s : ι → set Ω} {μ : measure Ω} :
  Indep_sets (λ i, {s i}) μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
forall_congr $ λ t,
  ⟨λ h, h $ λ _ _, mem_singleton _,
  λ h f hf, begin
    refine eq.trans _ (h.trans $ finset.prod_congr rfl $ λ i hi, congr_arg _ $ (hf i hi).symm),
    rw Inter₂_congr hf,
  end⟩

lemma Indep_set_iff_Indep_sets_singleton {s : ι → set Ω} (hs : ∀ i, measurable_set (s i))
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  Indep_set s μ ↔ Indep_sets (λ i, {s i}) μ :=
⟨Indep.Indep_sets $ λ _, rfl, Indep_sets.Indep _
  (λ i, generate_from_le $ by { rintro t (rfl : t = s i), exact hs _}) _
    (λ _, is_pi_system.singleton $ s _) $ λ _, rfl⟩

variables [is_probability_measure μ]

lemma Indep_set_iff_measure_Inter_eq_prod {s : ι → set Ω} (hs : ∀ i, measurable_set (s i)) :
  Indep_set s μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
(Indep_set_iff_Indep_sets_singleton hs μ).trans Indep_sets_singleton_iff

lemma Indep_sets.Indep_set_of_mem {s : ι → set Ω} {S : ι → set (set Ω)} (hs : ∀ i, s i ∈ S i)
  (hs_meas : ∀ i, measurable_set (s i)) (h_indep : Indep_sets S μ) :
  Indep_set s μ :=
(Indep_set_iff_measure_Inter_eq_prod hs_meas).2 $ λ t, h_indep _ $ λ i _, hs _

end probability_theory
