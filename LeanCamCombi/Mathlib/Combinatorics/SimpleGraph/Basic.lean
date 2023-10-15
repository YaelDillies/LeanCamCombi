import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.FunLike.Fintype
import LeanCamCombi.Mathlib.Logic.Basic

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
end SimpleGraph
