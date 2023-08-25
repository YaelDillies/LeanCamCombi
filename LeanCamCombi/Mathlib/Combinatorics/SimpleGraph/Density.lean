import Mathbin.Combinatorics.SimpleGraph.Density
import Project.Mathlib.Combinatorics.SimpleGraph.Subgraph

#align_import mathlib.combinatorics.simple_graph.density

open Finset

open scoped Classical

namespace SimpleGraph

variable {α : Type _} [Fintype α] (G : SimpleGraph α) [Fintype G.edgeSetEmbedding]

def fullEdgeDensity : ℚ :=
  G.edgeFinset.card / Fintype.card α

noncomputable def maxEdgeSubdensity : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun G' : G.Subgraph => G'.coe.fullEdgeDensity

end SimpleGraph

