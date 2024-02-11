import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.FunLike.Fintype

variable {α : Type*} {G H : SimpleGraph α}

namespace SimpleGraph

@[simp] lemma disjoint_edgeFinset [Fintype G.edgeSet] [Fintype H.edgeSet] :
    Disjoint G.edgeFinset H.edgeFinset ↔ Disjoint G H := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp] lemma edgeFinset_eq_empty [Fintype G.edgeSet] : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot, edgeFinset_inj]

@[simp] lemma edgeFinset_nonempty [Fintype G.edgeSet] : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty.ne]

end SimpleGraph
