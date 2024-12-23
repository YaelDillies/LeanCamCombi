import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import LeanCamCombi.GrowthInGroups.Constructible

namespace PrimeSpectrum
variable {R : Type*} [CommSemiring R]

lemma isRetroCompact_iff {U : Set (PrimeSpectrum R)} (hU : IsOpen U) :
    IsRetroCompact U ↔ IsCompact U := by
  refine isTopologicalBasis_basic_opens.isRetroCompact_iff_isCompact (fun i j ↦ ?_) hU
  rw [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul]
  exact isCompact_basicOpen _

end PrimeSpectrum
