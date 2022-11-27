import mathlib.measure
import probability.independence

open measure_theory measurable_space set
open_locale big_operators

namespace probability_theory
variables {Ω ι : Type*} [measurable_space Ω] {π : ι → set (set Ω)} {μ : measure Ω}

lemma Indep_sets.meas_Inter [fintype ι] (h : Indep_sets π μ) {f : ι → set Ω} (hf : ∀ i, f i ∈ π i) :
  μ (⋂ i, f i) = ∏ i, μ (f i) :=
by simp [← h _ (λ i _, hf _)]

lemma Indep_set.Indep_comap {s : ι → set Ω} (h : Indep_set s μ) :
  Indep (λ i, measurable_space.comap (∈ s i) ⊤) μ :=
by { simp_rw ←generate_from_singleton, exact h }

end probability_theory
