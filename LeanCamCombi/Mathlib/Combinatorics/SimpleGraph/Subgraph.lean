import Mathlib.Combinatorics.SimpleGraph.Subgraph

open Function

variable {α β γ V : Type*} {G H : SimpleGraph V}

namespace SimpleGraph

namespace Subgraph

/-- The subgraph of `H` corresponding to a smaller graph `H`. -/
@[simps]
def ofLE (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub := @h
  edge_vert _ := Set.mem_univ _
  symm := H.symm

open scoped Classical

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if they are adjacent
in `G`. -/
def IsInduced' (G' : Subgraph G) : Prop :=
  ∀ ⦃v w⦄, v ∈ G'.verts → w ∈ G'.verts → G.Adj v w → G'.Adj v w

@[simp] protected lemma IsInduced'.adj {G' : G.Subgraph} (hG' : G'.IsInduced') {a b : G'.verts} :
    G'.Adj a b ↔ G.Adj a b :=
  ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

end Subgraph
end SimpleGraph
