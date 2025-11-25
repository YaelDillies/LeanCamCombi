import Mathlib.Probability.HasLaw

open MeasureTheory

namespace ProbabilityTheory
variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X Y : Ω → 𝓧}
  {μ : Measure 𝓧} {P : Measure Ω}

attribute [fun_prop] HasLaw HasLaw.aemeasurable

lemma hasLaw_congr (hXY : X =ᵐ[P] Y) : HasLaw X μ P ↔ HasLaw Y μ P where
  mp h := h.congr hXY.symm
  mpr h := h.congr hXY

protected lemma HasLaw.ae_iff (hX : HasLaw X μ P) {p : 𝓧 → Prop} (hp : Measurable p) :
    (∀ᵐ ω ∂P, p (X ω)) ↔ ∀ᵐ x ∂μ, p x := by
  rw [← hX.map_eq, ae_map_iff hX.aemeasurable (measurableSet_setOf.2 hp)]

end ProbabilityTheory
