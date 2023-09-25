import Mathlib.Probability.Independence.Basic
import LeanCamCombi.Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory MeasurableSpace Set
open scoped BigOperators

namespace ProbabilityTheory

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  {π : ι → Set (Set Ω)} {μ : Measure Ω} {S : Finset ι} {s : ι → Set Ω} {f : ∀ i, Ω → β i}

lemma iIndepSets.meas_biInter (h : iIndepSets π μ) (hs : ∀ i, i ∈ S → s i ∈ π i) :
    μ (⋂ i ∈ S, s i) = ∏ i in S, μ (s i) := (iIndepSets_iff _ _).1 h _ hs

lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π μ) (hs : ∀ i, s i ∈ π i) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [←h.meas_biInter fun _ _ ↦ hs _]

lemma iIndep.meas_biInter {m : ι → MeasurableSpace Ω} (hμ : iIndep m μ)
  (hs : ∀ i, i ∈ S → MeasurableSet[m i] (s i)) :
    μ (⋂ i ∈ S, s i) = ∏ i in S, μ (s i) := (iIndep_iff _ _).1 hμ _ hs

lemma iIndep.meas_iInter [Fintype ι] {m : ι → MeasurableSpace Ω} (hμ : iIndep m μ)
  (hs : ∀ i, MeasurableSet[m i] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [←hμ.meas_biInter fun _ _ ↦ hs _]

protected lemma iIndep.iIndepSets' {m : ι → MeasurableSpace Ω} (hμ : iIndep m μ) :
    ProbabilityTheory.iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) μ :=
  (iIndep_iff_iIndepSets _ _).1 hμ

protected lemma iIndepFun.iIndep {m : ∀ i, MeasurableSpace (β i)} (hf : iIndepFun m f μ) :
    iIndep (fun x ↦ (m x).comap (f x)) μ := hf

lemma iIndepFun.meas_biInter {m : ∀ i, MeasurableSpace (β i)} (hf : iIndepFun m f μ)
  (hs : ∀ i, i ∈ S → MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i ∈ S, s i) = ∏ i in S, μ (s i) := hf.iIndep.meas_biInter hs

lemma iIndepFun.meas_iInter [Fintype ι] {m : ∀ i, MeasurableSpace (β i)} (hf : iIndepFun m f μ)
  (hs : ∀ i, MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := hf.iIndep.meas_iInter hs

lemma IndepFun.meas_inter {β γ : Type* } [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {f : Ω → β}
  {g : Ω → γ} (hfg : IndepFun f g μ) {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s)
  (ht : MeasurableSet[mγ.comap g] t) :
    μ (s ∩ t) = μ s * μ t := (IndepFun_iff _ _ _).1 hfg _ _ hs ht

lemma iIndep_comap_iff : iIndep (fun i ↦ MeasurableSpace.comap (· ∈ s i) ⊤) μ ↔ iIndepSet s μ := by
  simp_rw [←generateFrom_singleton]; rfl

alias ⟨_, iIndepSet.Indep_comap⟩ := iIndep_comap_iff

lemma iIndepSets_singleton_iff :
    iIndepSets (fun i ↦ {s i}) μ ↔ ∀ S, μ (⋂ i ∈ S, s i) = ∏ i in S, μ (s i) :=
  (iIndepSets_iff _ _).trans $ forall_congr' fun t ↦
    ⟨fun h ↦ h fun _ _ ↦ mem_singleton _, fun h f hf ↦ by
      refine'
        Eq.trans _ (h.trans $ Finset.prod_congr rfl fun i hi ↦ congr_arg _ $ (hf i hi).symm)
      rw [iInter₂_congr hf]⟩

lemma iIndepSet_iff_iIndepSets_singleton (hs : ∀ i, MeasurableSet (s i))
  (μ : Measure Ω := by volume_tac) [IsProbabilityMeasure μ] :
    iIndepSet s μ ↔ iIndepSets (fun i ↦ {s i}) μ :=
  ⟨iIndep.iIndepSets fun _ ↦ rfl,
    iIndepSets.iIndep _ (λ i ↦ generateFrom_le $ by rintro t (rfl : t = s i); exact hs _) _
      (λ _ => IsPiSystem.singleton $ s _) fun _ ↦ rfl⟩

variable [IsProbabilityMeasure μ]

lemma iIndepSet_iff_meas_iInter (hs : ∀ i, MeasurableSet (s i)) :
    iIndepSet s μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
  (iIndepSet_iff_iIndepSets_singleton hs μ).trans iIndepSets_singleton_iff

alias ⟨iIndepSet.meas_iInter, _⟩ := iIndepSet_iff_meas_iInter

lemma iIndepSets.iIndepSet_of_mem {S : ι → Set (Set Ω)} (hs : ∀ i, s i ∈ S i)
    (hs_meas : ∀ i, MeasurableSet (s i)) (h_indep : iIndepSets S μ) : iIndepSet s μ :=
  (iIndepSet_iff_meas_iInter hs_meas).2 fun _ ↦ h_indep.meas_biInter fun _ _ ↦ hs _

end ProbabilityTheory
