import Mathlib.Logic.Lemmas
import Mathlib.MeasureTheory.Measure.MeasureSpace
import LeanCamCombi.Mathlib.Data.Set.Image
import LeanCamCombi.Mathlib.Logic.Basic

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory

variable {α β : Type _} [MeasurableSpace β] {f g : α → β} {s : Set β}

namespace MeasureTheory
variable [MeasurableSpace α] {μ : Measure α}

namespace Measure

@[simp]
lemma map_eq_zero_iff (hf : AEMeasurable f μ) : μ.map f = 0 ↔ μ = 0 := by
  refine' ⟨fun h ↦ _, _⟩
  · replace h := congr_fun (congr_arg (↑) h) Set.univ
    rwa [map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ, coe_zero,
      Pi.zero_apply, measure_univ_eq_zero] at h
  · rintro rfl
    exact Measure.map_zero _

@[simp]
lemma mapₗ_eq_zero_iff (hf : Measurable f) : Measure.mapₗ f μ = 0 ↔ μ = 0 := by
  classical
  rw [←map_eq_zero_iff hf.aemeasurable, map, dif_pos hf.aemeasurable,
    mapₗ_congr hf hf.aemeasurable.measurable_mk]
  exact hf.aemeasurable.ae_eq_mk

lemma map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f ≠ 0 ↔ μ ≠ 0 := (map_eq_zero_iff hf).ne
lemma mapₗ_ne_zero_iff (hf : Measurable f) : Measure.mapₗ f μ ≠ 0 ↔ μ ≠ 0 := (mapₗ_eq_zero_iff hf).ne

end Measure

instance Prop.measurableSpace : MeasurableSpace Prop := ⊤
instance Prop.measurableSingletonClass : MeasurableSingletonClass Prop := ⟨fun _ ↦ trivial⟩

instance {α} : MeasurableSpace (Set α) := ⊤
instance {α} : MeasurableSingletonClass (Set α) := ⟨fun _ ↦ trivial⟩

instance isProbabilityMeasure_neZero {α : Type _} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] : NeZero μ :=
  ⟨IsProbabilityMeasure.ne_zero μ⟩

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

lemma comap_compl (h : Measurable (compl : β → β)) (f : α → β) :
    MeasurableSpace.comap (fun a ↦ (f a)ᶜ) inferInstance = MeasurableSpace.comap f inferInstance :=
  comap_of_involutive compl_involutive h _

@[simp]
lemma comap_not :
    MeasurableSpace.comap (fun a ↦ ¬ p a) inferInstance = MeasurableSpace.comap p inferInstance :=
  comap_compl (fun _ _ ↦ by trivial) _

end MeasurableSpace

lemma AEMeasurable.nullMeasurableSet_preimage [MeasurableSpace α] {μ : Measure α}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) : NullMeasurableSet (f ⁻¹' s) μ :=
  ⟨hf.mk _ ⁻¹' s, hf.measurable_mk hs, hf.ae_eq_mk.preimage _⟩

namespace MeasureTheory
variable [MeasurableSpace α] {μ : Measure α}

-- change `measure_compl` to `measurable_set.compl` in the `measure_theory` namespace
nonrec lemma NullMeasurableSet.measure_compl {s : Set α} (h : NullMeasurableSet s μ) (hs : μ s ≠ ∞) :
    μ sᶜ = μ Set.univ - μ s := by
  rw [←measure_congr h.toMeasurable_ae_eq, ←measure_compl (measurableSet_toMeasurable _ _)]
  · exact measure_congr h.toMeasurable_ae_eq.symm.compl
  · rwa [measure_congr h.toMeasurable_ae_eq]

lemma NullMeasurableSet.prob_compl_eq_one_sub [IsProbabilityMeasure μ] {s : Set α}
    (h : NullMeasurableSet s μ) : μ (sᶜ) = 1 - μ s := by
  rw [h.measure_compl (measure_ne_top _ _), measure_univ]

end MeasureTheory

namespace MeasurableSpace

/-- The sigma-algebra generated by a single set `s` is `{∅, s, sᶜ, univ}`. -/
@[simp]
lemma generateFrom_singleton (s : Set α) : generateFrom {s} = MeasurableSpace.comap (· ∈ s) ⊤ := by
  classical
  refine' le_antisymm (generateFrom_le fun t ht ↦ ⟨{True}, trivial, by simp [ht.symm]⟩) _
  rintro _ ⟨u, -, rfl⟩
  by_cases hu₁ : True ∈ u <;> by_cases hu₀ : False ∈ u
  · rw [(_ : u = univ), preimage_univ]
    · exact MeasurableSet.univ
    · rw [eq_univ_iff_forall, Prop.forall]
      exact ⟨hu₁, hu₀⟩
  · rw [(_ : u = {True}), preimage_mem_singleton_true]
    · exact GenerateMeasurable.basic _ (mem_singleton _)
    · simp [eq_singleton_iff_unique_mem, Prop.forall, hu₁, hu₀]
  · rw [(_ : u = {False}), preimage_mem_singleton_false]
    · exact GenerateMeasurable.compl _ (GenerateMeasurable.basic _ $ mem_singleton _)
    · simp [eq_singleton_iff_unique_mem, Prop.forall, hu₁, hu₀]
  · rw [(_ : u = ∅), preimage_empty]
    · exact @MeasurableSet.empty _ (generateFrom _)
    · simp [eq_empty_iff_forall_not_mem, Prop.forall, hu₁, hu₀]

end MeasurableSpace
