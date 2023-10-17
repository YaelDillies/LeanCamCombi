import Mathlib.Combinatorics.SimpleGraph.Subgraph
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Basic
import LeanCamCombi.Mathlib.Logic.Relation

-- attribute [protected] SimpleGraph.Subgraph.mem_edgeSet

open Function

variable {α β γ V : Type*} {G H : SimpleGraph V}

namespace SimpleGraph

namespace Subgraph

-- TODO: Replace `coe_Adj`
alias coe_adj := coe_Adj

instance (G : SimpleGraph V) (H : Subgraph G) [DecidableRel H.Adj] : DecidableRel H.coe.Adj :=
  fun a b ↦ ‹DecidableRel H.Adj› _ _

@[simp] lemma map_id {G : SimpleGraph α} (G' : G.Subgraph) : G'.map Hom.id = G' := by ext <;> simp

@[simp] lemma map_comp {G : SimpleGraph α} {H : SimpleGraph β} {I : SimpleGraph γ} (G' : G.Subgraph)
    (f : G →g H) (g : H →g I) : G'.map (g.comp f) = (G'.map f).map g := by
  ext <;> simp [Subgraph.map]

@[simp] lemma edgeSet_map {G : SimpleGraph α} {H : SimpleGraph β} (f : G →g H) (G' : G.Subgraph) :
    (G'.map f).edgeSet = Sym2.map f '' G'.edgeSet := by
  ext e
  induction' e using Sym2.ind with a b
  simp only [mem_edgeSet, Sym2.exists, Relation.Map, and_or_left, exists_or, map_adj,
    Set.mem_image, Sym2.map_pair_eq, Quotient.eq, Sym2.rel_iff]
  refine' (or_iff_left_of_imp _).symm
  rintro ⟨a, b, hab, rfl, rfl⟩
  exact ⟨b, a, hab.symm, rfl, rfl⟩

@[simp] lemma edgeSet_coe {G' : G.Subgraph} : G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet := by
  ext e; induction' e using Sym2.ind with a b; simp

lemma image_coe_edgeSet_coe (G' : G.Subgraph) : Sym2.map (↑) '' G'.coe.edgeSet = G'.edgeSet := by
  rw [edgeSet_coe, Set.image_preimage_eq_iff]
  rintro e he
  induction' e using Sym2.ind with a b
  rw [Subgraph.mem_edgeSet] at he
  exact ⟨⟦(⟨a, edge_vert _ he⟩, ⟨b, edge_vert _ he.symm⟩)⟧, Sym2.map_pair_eq _ _ _⟩

@[simp] lemma coe_bot : (⊥ : G.Subgraph).coe = ⊥ := rfl

lemma spanningCoe_le (G' : G.Subgraph) : G'.spanningCoe ≤ G := fun _ _ ↦ G'.3

/-- The subgraph of `H` corresponding to a smaller graph `H`. -/
@[simps]
def ofLe (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub := @h
  edge_vert _ := Set.mem_univ _
  symm := H.symm

/-- The graph isomorphism between the top element of `G.subgraph` and `G`. -/
@[simps]
def topIso : (⊤ : G.Subgraph).coe ≃g G where
  toFun := (↑)
  invFun a := ⟨a, Set.mem_univ _⟩
  left_inv _ := Subtype.eta _ _
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The isomorphism between a subgraph and its isomorphism under an injective map. -/
@[simps]
noncomputable def isoMap {H : SimpleGraph β} (f : G →g H) (hf : Injective f) (G' : G.Subgraph) :
    G'.coe ≃g (G'.map f).coe :=
  { Equiv.Set.image f G'.verts hf with map_rel_iff' := by dsimp; simp [hf] }

open scoped Classical

noncomputable instance [Fintype V] : Fintype G.Subgraph :=
  Fintype.ofEquiv
    {H : Set V × (V → V → Prop) // H.2 ≤ G.Adj ∧ (∀ a b, H.2 a b → a ∈ H.1) ∧ Symmetric H.2}
    { toFun := fun H ↦ ⟨H.1.1, H.1.2, @H.2.1, @H.2.2.1, H.2.2.2⟩
      invFun := fun H ↦ ⟨⟨H.1, H.2⟩, fun _ _ ↦ H.3, fun _ _ ↦ H.4, H.5⟩
      left_inv := fun {x} ↦ by ext <;> rfl
      right_inv := fun {x} ↦ by ext <;> rfl }

instance [Finite V] : Finite G.Subgraph := by cases nonempty_fintype V; infer_instance

@[simp] lemma isInduced_top : (⊤ : G.Subgraph).IsInduced := fun _ _ ↦ id

@[simp] protected lemma IsInduced.adj {G' : G.Subgraph} (hG' : G'.IsInduced) {a b : G'.verts} :
    G'.Adj a b ↔ G.Adj a b :=
  ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if they are adjacent
in `G`. -/
def IsInduced' (G' : Subgraph G) : Prop :=
  ∀ ⦃v w⦄, v ∈ G'.verts → w ∈ G'.verts → G.Adj v w → G'.Adj v w

@[simp] protected lemma IsInduced'.adj {G' : G.Subgraph} (hG' : G'.IsInduced') {a b : G'.verts} :
    G'.Adj a b ↔ G.Adj a b :=
  ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

end Subgraph
end SimpleGraph
