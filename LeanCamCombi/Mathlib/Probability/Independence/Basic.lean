import Mathlib.Probability.Independence.Basic

open MeasureTheory MeasurableSpace Set
open scoped BigOperators

namespace ProbabilityTheory

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  {π : ι → Set (Set Ω)} {μ : Measure Ω} {S : Finset ι} {s : ι → Set Ω} {f : ∀ i, Ω → β i}

lemma iIndep_comap_iff : iIndep (fun i ↦ MeasurableSpace.comap (· ∈ s i) ⊤) μ ↔ iIndepSet s μ := by
  simp_rw [←generateFrom_singleton]; rfl

alias ⟨_, iIndepSet.Indep_comap⟩ := iIndep_comap_iff

variable [IsProbabilityMeasure μ]

lemma iIndepSet_iff_meas_iInter (hs : ∀ i, MeasurableSet (s i)) :
    iIndepSet s μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i in t, μ (s i) :=
  (iIndepSet_iff_iIndepSets_singleton hs).trans iIndepSets_singleton_iff

alias ⟨iIndepSet.meas_iInter, _⟩ := iIndepSet_iff_meas_iInter

end ProbabilityTheory
