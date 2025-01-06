import Mathlib.Data.Set.Finite.Basic

namespace Set
variable {α : Type*} {s t u : Set α}

open scoped symmDiff

lemma Finite.symmDiff_congr (hst : (s ∆ t).Finite) : (s ∆ u).Finite ↔ (t ∆ u).Finite where
  mp hsu := (hst.union hsu).subset (symmDiff_comm s t ▸ symmDiff_triangle ..)
  mpr htu := (hst.union htu).subset (symmDiff_triangle ..)

end Set
