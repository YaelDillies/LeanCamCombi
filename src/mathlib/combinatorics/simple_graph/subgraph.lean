import mathlib.combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import mathlib.logic.relation

open function

variables {α β γ V : Type*} {G H : simple_graph V}

namespace simple_graph
namespace subgraph

instance (G : simple_graph V) (H : subgraph G) [decidable_rel H.adj] : decidable_rel H.coe.adj :=
λ a b, ‹decidable_rel H.adj› _ _

@[simp] lemma map_id {G : simple_graph α} (G' : G.subgraph) : G'.map hom.id = G' := by ext; simp

@[simp] lemma map_comp {G : simple_graph α} {H : simple_graph α} {I : simple_graph α}
  (G' : G.subgraph) (f : G →g H) (g : H →g I) :
  G'.map (g.comp f) = (G'.map f).map g :=
by ext; simp [subgraph.map]

lemma spanning_coe_le (G' : G.subgraph) : G'.spanning_coe ≤ G := λ a b, G'.3

/-- The subgraph of `H` corresponding to a smaller graph `H`. -/
@[simps] def of_le (h : H ≤ G) : G.subgraph :=
{ verts := set.univ,
  adj := H.adj,
  adj_sub := h,
  edge_vert := λ _ _ _, set.mem_univ _,
  symm := H.symm }

/-- The graph isomorphism between the top element of `G.subgraph` and `G`. -/
@[simps] def top_iso : (⊤ : G.subgraph).coe ≃g G :=
{ to_fun := coe,
  inv_fun := λ a, ⟨a, set.mem_univ _⟩,
  left_inv := λ _, subtype.eta _ _,
  right_inv := λ _, rfl,
  map_rel_iff' := λ _ _, iff.rfl }

open_locale classical

noncomputable instance [fintype V] : fintype G.subgraph :=
fintype.of_equiv
  {H : set V × (V → V → Prop) // H.2 ≤ G.adj ∧ (∀ a b, H.2 a b → a ∈ H.1) ∧ symmetric H.2}
  { to_fun := λ H, ⟨H.1.1, H.1.2, H.2.1, H.2.2.1, H.2.2.2⟩,
    inv_fun := λ H, ⟨⟨H.1, H.2⟩, λ _ _, H.3, λ _ _, H.4, H.5⟩,
    left_inv := λ _, by ext; refl,
    right_inv := λ _, by ext; refl }

instance [finite V] : finite G.subgraph := by { casesI nonempty_fintype V, apply_instance }

end subgraph
end simple_graph
