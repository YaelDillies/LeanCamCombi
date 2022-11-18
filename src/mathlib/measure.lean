
import measure_theory.measure.measure_space

open measure_theory

variables {α β : Type*} [measurable_space α] [measurable_space β] {μ : measure α} {f : α → β}

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

end measure
end measure_theory
