import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.FunLike.Fintype
import LeanCamCombi.Mathlib.Logic.Basic

/-!
John Talbot found dealing with the mathlib induced subgraph too painful.
-/

open Set

variable {α β : Type*} {G H : SimpleGraph α} {s : Set (Sym2 α)}

namespace SimpleGraph

instance [Subsingleton α] : Unique (SimpleGraph α) where
  default := ⊥
  uniq G := by ext a b; have := Subsingleton.elim a b; simp [this]

instance [Nontrivial α] : Nontrivial (SimpleGraph α) :=
  ⟨⟨⊥, ⊤, fun h ↦ not_subsingleton α ⟨by simpa only [←adj_inj, Function.funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩⟩

@[simp] lemma disjoint_edgeSet : Disjoint G.edgeSet H.edgeSet ↔ Disjoint G H := by
  rw [Set.disjoint_iff, disjoint_iff_inf_le, ←edgeSet_inf, ←edgeSet_bot, ←Set.le_iff_subset,
    OrderEmbedding.le_iff_le]

@[simp] lemma nonempty_edgeSet : G.edgeSet.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, ←edgeSet_bot,  edgeSet_inj.ne]

@[simp] lemma disjoint_fromEdgeSet : Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s := by
  conv_rhs => rw [←Set.diff_union_inter s {e : Sym2 α | e.IsDiag}]
  rw [←disjoint_edgeSet,  edgeSet_fromEdgeSet, Set.disjoint_union_right, and_iff_left]
  exact Set.disjoint_left.2 fun e he he' ↦ not_isDiag_of_mem_edgeSet _ he he'.2

@[simp] lemma fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet := by
  rw [disjoint_comm, disjoint_fromEdgeSet, disjoint_comm]

@[simp] lemma deleteEdges_eq : G.deleteEdges s = G ↔ Disjoint G.edgeSet s := by
  rw [deleteEdges_eq_sdiff_fromEdgeSet, sdiff_eq_left, disjoint_fromEdgeSet]

namespace Hom

-- TODO: Protect `Hom.id`
@[simp, norm_cast] lemma coe_id : ⇑(id : G →g G) = _root_.id := rfl

instance [Subsingleton (α → β)] {H : SimpleGraph β} : Subsingleton (G →g H) :=
  FunLike.coe_injective.subsingleton

instance [IsEmpty α] {H : SimpleGraph β} : Unique (G →g H) where
  default := ⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _

noncomputable instance [Fintype α] [Fintype β] {H : SimpleGraph β} : Fintype (G →g H) := by
  classical exact FunLike.fintype _

instance [Finite α] [Finite β] {H : SimpleGraph β} : Finite (G →g H) := FunLike.finite _

end Hom

/-- The graph homomorphism from a smaller graph to a bigger one. -/
def homOfLe (h : G ≤ H) : G →g H := ⟨id, @h⟩

@[simp, norm_cast] lemma coe_homOfLe (h : G ≤ H) : ⇑(homOfLe h) = id := rfl

namespace Embedding

attribute [simp] map_adj_iff

@[simp] lemma coe_toHom {H : SimpleGraph β} (f : G ↪g H) : ⇑f.toHom = f := rfl

end Embedding


@[simp]
lemma disjoint_edgeFinset [Fintype G.edgeSet] [Fintype H.edgeSet] :
    Disjoint G.edgeFinset H.edgeFinset ↔ Disjoint G H := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp]
lemma edgeFinset_eq_empty [Fintype G.edgeSet] : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot, edgeFinset_inj]

@[simp]
lemma nonempty_edgeFinset [Fintype G.edgeSet] : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty.ne]

@[simp] lemma deleteEdges_edgeSet (G H : SimpleGraph α) : G.deleteEdges H.edgeSet = G \ H := rfl

section Ind
variable {s t : Set α} {a b : α}

/-- Graph induced by s:finset α, defined to be a simple_graph α (so all vertices outside s have
empty neighborhoods). this is equivalent to  "spanning_coe (induce (s:set α) G)" as we prove below.
-/
def ind (G : SimpleGraph α) (s : Set α) : SimpleGraph α where
  Adj a b := G.Adj a b ∧ a ∈ s ∧ b ∈ s
  symm a b hab := ⟨hab.1.symm, hab.2.2, hab.2.1⟩

@[simp]
lemma adj_ind : (G.ind s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s :=
  Iff.rfl

@[simp]
lemma ind_empty (G : SimpleGraph α) : G.ind ∅ = ⊥ := by ext; simp

@[simp]
lemma ind_univ (G : SimpleGraph α) : G.ind univ = G := by ext; simp

@[simp]
lemma ind_singleton (G : SimpleGraph α) (a : α) : G.ind {a} = ⊥ := by
  ext; simp; rintro h rfl; exact h.ne'

@[simp]
lemma ind_inter (G : SimpleGraph α) (s t : Set α) : G.ind (s ∩ t) = G.ind s ⊓ G.ind t := by
  ext; simp; tauto

@[simp]
lemma spanningCoe_induce (G : SimpleGraph α) (s : Set α) :
    spanningCoe (induce (s : Set α) G) = G.ind s := by ext; simp [← and_assoc]

/-- Induced subgraphs on disjoint sets meet in the empty graph. -/
lemma disjoint_ind (h : Disjoint s t) : Disjoint (G.ind s) (G.ind t) := by
  rw [disjoint_iff, ← ind_inter, disjoint_iff_inter_eq_empty.1 h, ind_empty]

end Ind
end SimpleGraph
