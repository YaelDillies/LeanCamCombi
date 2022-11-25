import probability.independence

open measure_theory
open_locale big_operators

namespace probability_theory
variables {Ω ι : Type*} [measurable_space Ω] {π : ι → set (set Ω)} {μ : measure Ω}

lemma Indep_sets.meas_Inter [fintype ι] (h : Indep_sets π μ) {f : ι → set Ω} (hf : ∀ i, f i ∈ π i) :
  μ (⋂ i, f i) = ∏ i, μ (f i) :=
by simp [← h _ (λ i _, hf _)]

#check measurable_space.comap

-- lemma Indep_set.Indep_generate_from {s : ι → set Ω} (h : Indep_set s μ) :
--   Indep (λ i, measurable_space.generate_from {s i}) μ :=
-- begin
--   exact h,
-- end

lemma Prop.forall_iff {f : Prop → Prop} : (∀ p, f p) ↔ f true ∧ f false :=
begin
  refine ⟨λ h, ⟨h _, h _⟩, λ h p, _⟩,
  by_cases hp : p,
  simpa [hp] using h.1,
  simpa [hp] using h.2,
end

lemma measurable_space.comap_singleton_eq_generate_from {s : set Ω} :
  measurable_space.comap (∈ s) ⊤ = measurable_space.generate_from {s} :=
begin
  classical,
  ext t,
  split,
  { rintro ⟨u, -, rfl⟩,
    by_cases hu₁ : true ∈ u; by_cases hu₀ : false ∈ u,
    { rw [(_ : u = set.univ), set.preimage_univ],
      { exact measurable_set.univ },
      { rw [set.eq_univ_iff_forall, Prop.forall_iff],
        exact ⟨hu₁, hu₀⟩ } },
    { rw [(_ : u = {true}), (_ : (∈ s) ⁻¹' {true} = s)],
      { refine generate_from_measurable_set

      }
     },
    { sorry },
    { sorry } },
  sorry
end

lemma Indep_sets.Indep_comap {s : ι → set Ω} (h : Indep_set s μ) :
  Indep (λ i, measurable_space.comap (∈ s i) ⊤) μ :=
begin
  sorry
end

end probability_theory
