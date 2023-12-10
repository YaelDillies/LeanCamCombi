import Mathlib.Logic.Lemmas
import Mathlib.MeasureTheory.Measure.MeasureSpace

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory

variable {α β : Type*} [MeasurableSpace β] {f g : α → β} {s : Set β}

namespace MeasureTheory
variable [MeasurableSpace α] {μ : Measure α}

namespace Measure

@[simp] lemma map_eq_zero_iff (hf : AEMeasurable f μ) : μ.map f = 0 ↔ μ = 0 := by
  refine' ⟨fun h ↦ _, _⟩
  · replace h := congr_fun (congr_arg (↑) h) Set.univ
    rwa [map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ, coe_zero,
      Pi.zero_apply, measure_univ_eq_zero] at h
  · rintro rfl
    exact Measure.map_zero _

@[simp] lemma mapₗ_eq_zero_iff (hf : Measurable f) : Measure.mapₗ f μ = 0 ↔ μ = 0 := by
  classical
  rw [←map_eq_zero_iff hf.aemeasurable, map, dif_pos hf.aemeasurable,
    mapₗ_congr hf hf.aemeasurable.measurable_mk]
  exact hf.aemeasurable.ae_eq_mk

lemma map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f ≠ 0 ↔ μ ≠ 0 := (map_eq_zero_iff hf).not
lemma mapₗ_ne_zero_iff (hf : Measurable f) : Measure.mapₗ f μ ≠ 0 ↔ μ ≠ 0 :=
  (mapₗ_eq_zero_iff hf).not

end Measure

end MeasureTheory

namespace MeasurableSpace
variable [BooleanAlgebra β] (p : α → Prop)

lemma comap_of_involutive {g : β → β} (hg : Involutive g) (hg' : Measurable g) (f : α → β) :
    MeasurableSpace.comap (fun a ↦ g (f a)) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  ext
  set e : Set β ≃ Set β :=
    { toFun := preimage g
      invFun := preimage g
      left_inv := hg.preimage
      right_inv := hg.preimage }
  refine' e.exists_congr_left.trans (exists_congr fun t ↦ _)
  simp only [preimage_preimage, compl_compl, Equiv.coe_fn_symm_mk, and_congr_left_iff, hg _]
  rintro rfl
  refine' ⟨fun ht ↦ _, fun ht ↦ hg' ht⟩
  convert hg' ht
  simp_rw [preimage_preimage, hg _, preimage_id']

end MeasurableSpace

lemma AEMeasurable.nullMeasurableSet_preimage [MeasurableSpace α] {μ : Measure α}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) : NullMeasurableSet (f ⁻¹' s) μ :=
  ⟨hf.mk _ ⁻¹' s, hf.measurable_mk hs, hf.ae_eq_mk.preimage _⟩

namespace MeasureTheory
variable [MeasurableSpace α] {μ : Measure α} {s : Set α}

nonrec lemma NullMeasurableSet.measure_compl (h : NullMeasurableSet s μ) (hs : μ s ≠ ∞) :
    μ sᶜ = μ Set.univ - μ s := by
  rw [←measure_congr h.toMeasurable_ae_eq, ←measure_compl (measurableSet_toMeasurable _ _)]
  · exact measure_congr h.toMeasurable_ae_eq.symm.compl
  · rwa [measure_congr h.toMeasurable_ae_eq]

end MeasureTheory
