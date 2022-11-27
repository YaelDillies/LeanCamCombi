import combinatorics.simple_graph.subgraph

open function

variables {V : Type*} {G H : simple_graph V}

namespace simple_graph

lemma edge_set_injective : injective (edge_set : simple_graph V → set (sym2 V)) :=
λ G H h, by { ext a b, simpa using set.ext_iff.1 h ⟦(a, b)⟧ }

@[simp] lemma edge_set_inj : G.edge_set = H.edge_set ↔ G = H := edge_set_injective.eq_iff

@[simp] lemma edge_finset_inj [fintype G.edge_set] [fintype H.edge_set] :
  G.edge_finset = H.edge_finset ↔ G = H :=
by simp_rw [←finset.coe_inj, coe_edge_finset, edge_set_inj]

instance (G : simple_graph V) (H : subgraph G) [decidable_rel H.adj] : decidable_rel H.coe.adj :=
λ a b, ‹decidable_rel H.adj› _ _

end simple_graph
