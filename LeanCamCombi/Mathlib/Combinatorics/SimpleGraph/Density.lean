import Mathlib.Algebra.Field.Rat
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# TODO

Rename `edgeDensity` to `edgeDensityBtw`
-/

open Finset

namespace SimpleGraph
variable {α : Type*} [Fintype α] (G : SimpleGraph α) [Fintype G.edgeSet]

/-- The edge density of a simple graph is its number of edges divided by its number of vertices.

In other words, it is half of its average degree. -/
def edgeDensity' : ℚ≥0 := #G.edgeFinset / Fintype.card α

open scoped Classical in
/-- The maximum edge density of a subgraph of a graph. -/
noncomputable def maxEdgeSubdensity : ℚ≥0 :=
  univ.sup' univ_nonempty fun G' : G.Subgraph ↦ G'.coe.edgeDensity'

end SimpleGraph
