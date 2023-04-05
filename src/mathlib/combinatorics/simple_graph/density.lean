import combinatorics.simple_graph.density
import mathlib.combinatorics.simple_graph.subgraph

open finset
open_locale classical

namespace simple_graph
variables {α : Type*} [fintype α] (G : simple_graph α) [fintype G.edge_set]

def full_edge_density : ℚ := G.edge_finset.card / fintype.card α

noncomputable def max_edge_subdensity : ℚ :=
finset.univ.sup' finset.univ_nonempty $ λ G' : G.subgraph, G'.coe.full_edge_density


end simple_graph
