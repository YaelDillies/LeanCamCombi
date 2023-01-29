import mathlib.combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import mathlib.logic.relation

attribute [protected] simple_graph.subgraph.mem_edge_set

open function

variables {α β γ V : Type*} {G H : simple_graph V}

namespace simple_graph
namespace subgraph

instance (G : simple_graph V) (H : subgraph G) [decidable_rel H.adj] : decidable_rel H.coe.adj :=
λ a b, ‹decidable_rel H.adj› _ _

@[simp] lemma map_id {G : simple_graph α} (G' : G.subgraph) : G'.map hom.id = G' := by ext; simp

@[simp] lemma map_comp {G : simple_graph α} {H : simple_graph β} {I : simple_graph γ}
  (G' : G.subgraph) (f : G →g H) (g : H →g I) :
  G'.map (g.comp f) = (G'.map f).map g :=
by ext; simp [subgraph.map]

@[simp] lemma edge_set_map {G : simple_graph α} {H : simple_graph β} (f : G →g H)
  (G' : G.subgraph) : (G'.map f).edge_set = sym2.map f '' G'.edge_set :=
begin
  ext e,
  induction e using sym2.ind with a b,
  simp only [mem_edge_set, sym2.exists, relation.map, and_or_distrib_left, exists_or_distrib,
    map_adj, set.mem_image, sym2.map_pair_eq, quotient.eq, sym2.rel_iff],
  refine (or_iff_left_of_imp _).symm,
  rintro ⟨a, b, hab, rfl, rfl⟩,
  exact ⟨b, a, hab.symm, rfl, rfl⟩,
end

@[simp] lemma edge_set_coe {G' : G.subgraph} : G'.coe.edge_set = sym2.map coe ⁻¹' G'.edge_set :=
by { ext e, induction e using sym2.ind with a b, simp }

lemma image_coe_edge_set_coe (G' : G.subgraph) : sym2.map coe '' G'.coe.edge_set = G'.edge_set :=
begin
  rw [edge_set_coe, set.image_preimage_eq_iff],
  rintro e he,
  induction e using sym2.ind with a b,
  rw subgraph.mem_edge_set at he,
  exact ⟨⟦(⟨a, edge_vert _ he⟩, ⟨b, edge_vert _ he.symm⟩)⟧, sym2.map_pair_eq _ _ _⟩,
end

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

/-- The isomorphism between a subgraph and its isomorphism under an injective map. -/
@[simps]
noncomputable def iso_map {H : simple_graph β} (f : G →g H) (hf : injective f) (G' : G.subgraph) :
  G'.coe ≃g (G'.map f).coe :=
{ map_rel_iff' := λ a b, by simp [hf],
  ..equiv.set.image f G'.verts hf }

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
