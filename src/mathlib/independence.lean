import probability.independence

open measure_theory
open_locale big_operators

namespace probability_theory
variables {Ω ι : Type*} [measurable_space Ω] {π : ι → set (set Ω)} {μ : measure Ω}

lemma Indep_sets.meas_Inter [fintype ι] (h : Indep_sets π μ) {f : ι → set Ω} (hf : ∀ i, f i ∈ π i) :
  μ (⋂ i, f i) = ∏ i, μ (f i) :=
by simp [←h _ (λ i _, hf _)]

end probability_theory
