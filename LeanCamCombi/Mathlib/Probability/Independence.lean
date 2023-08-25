import Project.Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathbin.Probability.Independence.Basic

#align_import mathlib.probability.independence

open MeasureTheory MeasurableSpace Set

open scoped BigOperators

namespace ProbabilityTheory

variable {Ω ι : Type _} [MeasurableSpace Ω] {π : ι → Set (Set Ω)} {μ : Measure Ω}

theorem iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π μ) {f : ι → Set Ω}
    (hf : ∀ i, f i ∈ π i) : μ (⋂ i, f i) = ∏ i, μ (f i) := by simp [← h _ fun i _ => hf _]

theorem iIndep_comap_iff {s : ι → Set Ω} :
    iIndep (fun i => MeasurableSpace.comap (· ∈ s i) ⊤) μ ↔ iIndepSet s μ := by
  simp_rw [← generate_from_singleton]; rfl

alias ⟨_, Indep_set.Indep_comap⟩ := Indep_comap_iff

theorem iIndepSets_singleton_iff {s : ι → Set Ω} {μ : Measure Ω} :
    iIndepSets (fun i => {s i}) μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
  forall_congr' fun t =>
    ⟨fun h => h fun _ _ => mem_singleton _, fun h f hf =>
      by
      refine'
        Eq.trans _ (h.trans <| Finset.prod_congr rfl fun i hi => congr_arg _ <| (hf i hi).symm)
      rw [Inter₂_congr hf]⟩

theorem iIndepSet_iff_iIndepSets_singleton {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) [IsProbabilityMeasure μ] :
    iIndepSet s μ ↔ iIndepSets (fun i => {s i}) μ :=
  ⟨iIndep.iIndepSets fun _ => rfl,
    IndepSets.indep _ (fun i => generateFrom_le <| by rintro t (rfl : t = s i); exact hs _) _
      (fun _ => IsPiSystem.singleton <| s _) fun _ => rfl⟩

variable [IsProbabilityMeasure μ]

theorem iIndepSet_iff_measure_iInter_eq_prod {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i)) :
    iIndepSet s μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
  (iIndepSet_iff_iIndepSets_singleton hs μ).trans iIndepSets_singleton_iff

theorem iIndepSets.iIndepSet_of_mem {s : ι → Set Ω} {S : ι → Set (Set Ω)} (hs : ∀ i, s i ∈ S i)
    (hs_meas : ∀ i, MeasurableSet (s i)) (h_indep : iIndepSets S μ) : iIndepSet s μ :=
  (iIndepSet_iff_measure_iInter_eq_prod hs_meas).2 fun t => h_indep _ fun i _ => hs _

end ProbabilityTheory

