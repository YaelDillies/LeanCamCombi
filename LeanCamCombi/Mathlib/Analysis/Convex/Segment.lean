import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Real
variable {ε r : ℝ}

open Metric

lemma closedBall_eq_segment (hε : 0 ≤ ε) : closedBall r ε = segment ℝ (r - ε) (r + ε) := by
  rw [closedBall_eq_Icc, segment_eq_Icc ((sub_le_self _ hε).trans $ le_add_of_nonneg_right hε)]

end Real
