import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Subgraph

open Finset
open scoped Classical

namespace SimpleGraph
variable {α : Type*} [Fintype α] (G : SimpleGraph α) [Fintype G.edgeSet]

def fullEdgeDensity : ℚ := #G.edgeFinset / Fintype.card α

noncomputable def maxEdgeSubdensity : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun G' : G.Subgraph ↦ G'.coe.fullEdgeDensity

end SimpleGraph
