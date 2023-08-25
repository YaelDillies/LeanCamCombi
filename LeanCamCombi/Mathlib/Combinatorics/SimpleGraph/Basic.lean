import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Data.FunLike.Fintype
import Project.Mathlib.Logic.Basic

#align_import mathlib.combinatorics.simple_graph.basic

variable {α β : Type _} {G H : SimpleGraph α} {s : Set (Sym2 α)}

namespace SimpleGraph

instance [Subsingleton α] : Unique (SimpleGraph α)
    where
  default := ⊥
  uniq G := by ext a b; simp [Subsingleton.elim a b]

instance [Nontrivial α] : Nontrivial (SimpleGraph α) :=
  ⟨⟨⊥, ⊤, fun h => not_subsingleton α ⟨by simpa [ext_iff, Function.funext_iff] using h⟩⟩⟩

@[simp]
theorem disjoint_edgeSetEmbedding : Disjoint G.edgeSetEmbedding H.edgeSetEmbedding ↔ Disjoint G H :=
  by
  rw [Set.disjoint_iff, disjoint_iff_inf_le, ← edge_set_inf, ← edge_set_bot, ← Set.le_iff_subset,
    OrderEmbedding.le_iff_le]

@[simp]
theorem nonempty_edgeSetEmbedding : G.edgeSetEmbedding.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, ← edge_set_bot, edge_set_inj.ne]

@[simp]
theorem disjoint_fromEdgeSet : Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSetEmbedding s :=
  by
  conv_rhs => rw [← Set.diff_union_inter s {e : Sym2 α | e.IsDiag}]
  rw [← disjoint_edge_set, edge_set_from_edge_set, Set.disjoint_union_right, and_iff_left]
  exact Set.disjoint_left.2 fun e he he' => not_is_diag_of_mem_edge_set _ he he'.2

@[simp]
theorem fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSetEmbedding := by
  rw [disjoint_comm, disjoint_from_edge_set, disjoint_comm]

@[simp]
theorem deleteEdges_eq : G.deleteEdges s = G ↔ Disjoint G.edgeSetEmbedding s := by
  rw [delete_edges_eq_sdiff_from_edge_set, sdiff_eq_left, disjoint_from_edge_set]

namespace Hom

@[simp, norm_cast]
theorem coe_id : ⇑(id : G →g G) = id :=
  rfl

instance [Subsingleton (α → β)] {H : SimpleGraph β} : Subsingleton (G →g H) :=
  FunLike.coe_injective.Subsingleton

instance [IsEmpty α] {H : SimpleGraph β} : Unique (G →g H)
    where
  default := ⟨isEmptyElim, isEmptyElim⟩
  uniq _ := Subsingleton.elim _ _

noncomputable instance [Fintype α] [Fintype β] {H : SimpleGraph β} : Fintype (G →g H) := by
  classical exact FunLike.fintype _

instance [Finite α] [Finite β] {H : SimpleGraph β} : Finite (G →g H) :=
  FunLike.finite _

end Hom

/-- The graph homomorphism from a smaller graph to a bigger one. -/
def homOfLe (h : G ≤ H) : G →g H :=
  ⟨id, h⟩

@[simp, norm_cast]
theorem coe_homOfLe (h : G ≤ H) : ⇑(homOfLe h) = id :=
  rfl

namespace Embedding

attribute [simp] map_adj_iff

@[simp]
theorem coe_toHom {H : SimpleGraph β} (f : G ↪g H) : ⇑f.toHom = f :=
  rfl

end Embedding

end SimpleGraph

