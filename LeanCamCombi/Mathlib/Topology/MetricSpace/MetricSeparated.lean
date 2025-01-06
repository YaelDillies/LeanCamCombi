import Mathlib.Topology.MetricSpace.MetricSeparated

/-!
# TODO

Rename `IsMetricSeparated` to `Metric.AreSeparated`
-/

open scoped ENNReal

namespace Metric
variable {X : Type*} [EMetricSpace X] {ε : ℝ≥0∞} {s t : Set X}

def IsSeparated (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)

end Metric
