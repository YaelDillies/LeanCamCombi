import combinatorics.simple_graph.subgraph

open function

variables {V : Type*} {G H : simple_graph V}

namespace simple_graph

instance (G : simple_graph V) (H : subgraph G) [decidable_rel H.adj] : decidable_rel H.coe.adj :=
λ a b, ‹decidable_rel H.adj› _ _

end simple_graph
