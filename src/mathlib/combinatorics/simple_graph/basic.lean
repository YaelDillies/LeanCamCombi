import combinatorics.simple_graph.basic
import mathlib.logic.basic

variables {α : Type*} {G H : simple_graph α}

namespace simple_graph

@[simp] lemma disjoint_edge_set : disjoint G.edge_set H.edge_set ↔ disjoint G H :=
by rw [set.disjoint_iff, disjoint_iff_inf_le, ←edge_set_inf, ←edge_set_bot, ←set.le_iff_subset,
  order_embedding.le_iff_le]

@[simp] lemma nonempty_edge_set : G.edge_set.nonempty ↔ G ≠ ⊥ :=
by rw [set.nonempty_iff_ne_empty, ←edge_set_bot, edge_set_inj.ne]

namespace hom

@[simp, norm_cast] lemma coe_id : ⇑(id : G →g G) = _root_.id := rfl

end hom

/-- The graph homomorphism from a smaller graph to a bigger one. -/
def hom_of_le (h : G ≤ H) : G →g H := ⟨id, h⟩

@[simp, norm_cast] lemma coe_hom_of_le (h : G ≤ H) : ⇑(hom_of_le h) = id := rfl

end simple_graph
