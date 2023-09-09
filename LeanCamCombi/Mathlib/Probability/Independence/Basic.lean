import Mathlib.Probability.Independence.Basic
import LeanCamCombi.Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory MeasurableSpace Set
open scoped BigOperators

namespace ProbabilityTheory

variable {Ω ι : Type _} [MeasurableSpace Ω] {π : ι → Set (Set Ω)} {μ : Measure Ω}

lemma iIndepSets.meas_biInter (h : iIndepSets π μ) {s : Finset ι} {f : ι → Set Ω}
    (hf : ∀ i, i ∈ s → f i ∈ π i) :
    μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i) := (iIndepSets_iff _ _).1 h _ hf

lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π μ) {f : ι → Set Ω}
    (hf : ∀ i, f i ∈ π i) : μ (⋂ i, f i) = ∏ i, μ (f i) := by simp [←h.meas_biInter fun _ _ ↦ hf _]

lemma iIndep_comap_iff {s : ι → Set Ω} :
    iIndep (fun i ↦ MeasurableSpace.comap (· ∈ s i) ⊤) μ ↔ iIndepSet s μ := by
  simp_rw [←generateFrom_singleton]; rfl

alias ⟨_, iIndepSet.Indep_comap⟩ := iIndep_comap_iff

lemma iIndepSets_singleton_iff {s : ι → Set Ω} {μ : Measure Ω} :
    iIndepSets (fun i ↦ {s i}) μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
  (iIndepSets_iff _ _).trans $ forall_congr' fun t ↦
    ⟨fun h ↦ h fun _ _ ↦ mem_singleton _, fun h f hf ↦ by
      refine'
        Eq.trans _ (h.trans $ Finset.prod_congr rfl fun i hi ↦ congr_arg _ $ (hf i hi).symm)
      rw [iInter₂_congr hf]⟩

lemma iIndepSet_iff_iIndepSets_singleton {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω := by volume_tac) [IsProbabilityMeasure μ] :
    iIndepSet s μ ↔ iIndepSets (fun i ↦ {s i}) μ :=
  ⟨iIndep.iIndepSets fun _ ↦ rfl,
    iIndepSets.iIndep _ (fun i => generateFrom_le <| by rintro t (rfl : t = s i); exact hs _) _
      (fun _ => IsPiSystem.singleton <| s _) fun _ => rfl⟩

variable [IsProbabilityMeasure μ]

lemma iIndepSet_iff_measure_iInter_eq_prod {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i)) :
    iIndepSet s μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
  (iIndepSet_iff_iIndepSets_singleton hs μ).trans iIndepSets_singleton_iff

lemma iIndepSets.iIndepSet_of_mem {s : ι → Set Ω} {S : ι → Set (Set Ω)} (hs : ∀ i, s i ∈ S i)
    (hs_meas : ∀ i, MeasurableSet (s i)) (h_indep : iIndepSets S μ) : iIndepSet s μ :=
  (iIndepSet_iff_measure_iInter_eq_prod hs_meas).2 fun _ ↦ h_indep.meas_biInter fun _ _ ↦ hs _

end ProbabilityTheory
