import measure_theory.measure.measure_space

open measure_theory

variables {α β : Type*} [measurable_space α] [measurable_space β] {μ : measure α} {f g : α → β}
  {s : set β}

namespace measure_theory
namespace measure

@[simp] lemma map_eq_zero_iff (hf : ae_measurable f μ) : μ.map f = 0 ↔ μ = 0 :=
begin
  refine ⟨λ h, _, _⟩,
  { replace h := congr_fun (congr_arg coe_fn h) set.univ,
    rwa [map_apply_of_ae_measurable hf measurable_set.univ, set.preimage_univ, coe_zero,
      pi.zero_apply, measure_univ_eq_zero] at h },
  { rintro rfl,
    exact measure.map_zero _ }
end

@[simp] lemma mapₗ_eq_zero_iff (hf : measurable f) : measure.mapₗ f μ = 0 ↔ μ = 0 :=
begin
  classical,
  rw [← map_eq_zero_iff hf.ae_measurable, map, dif_pos hf.ae_measurable,
    mapₗ_congr hf hf.ae_measurable.measurable_mk],
  exact hf.ae_measurable.ae_eq_mk,
end

lemma map_ne_zero_iff (hf : ae_measurable f μ) : μ.map f ≠ 0 ↔ μ ≠ 0 := (map_eq_zero_iff hf).not
lemma mapₗ_ne_zero_iff (hf : measurable f) : measure.mapₗ f μ ≠ 0 ↔ μ ≠ 0 :=
(mapₗ_eq_zero_iff hf).not

end measure

instance : measurable_space Prop := ⊤

instance : measurable_singleton_class Prop := ⟨λ _, trivial⟩

instance is_probability_measure_ne_zero {α : Type*} [measurable_space α] {μ : measure α}
  [is_probability_measure μ] : ne_zero μ :=
⟨is_probability_measure.ne_zero μ⟩

end measure_theory

-- Unused
@[simp] lemma set.preimage_symm_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
by simp [symm_diff]

lemma ae_measurable.null_measurable_set_preimage (hf : ae_measurable f μ) (hs : measurable_set s) :
  null_measurable_set (f ⁻¹' s) μ :=
⟨hf.mk _ ⁻¹' s, hf.measurable_mk hs, hf.ae_eq_mk.preimage _⟩
