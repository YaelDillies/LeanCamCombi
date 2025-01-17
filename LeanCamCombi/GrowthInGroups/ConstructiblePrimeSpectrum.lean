import Mathlib.RingTheory.Spectrum.Prime.Topology
import LeanCamCombi.GrowthInGroups.Constructible

namespace PrimeSpectrum
variable {R : Type*} [CommSemiring R]

lemma isRetrocompact_iff {U : Set (PrimeSpectrum R)} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsCompact U := by
  refine isTopologicalBasis_basic_opens.isRetrocompact_iff_isCompact ?_ hU
  simpa [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul, -basicOpen_eq_zeroLocus_compl]
    using fun _ _ ↦ isCompact_basicOpen _

end PrimeSpectrum
