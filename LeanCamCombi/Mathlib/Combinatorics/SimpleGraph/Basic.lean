import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.FunLike.Fintype

/-!
John Talbot found dealing with the mathlib induced subgraph too painful.
-/

open Set

variable {α β : Type*} {G H : SimpleGraph α} {s : Set (Sym2 α)}

namespace SimpleGraph

@[simp]
lemma disjoint_edgeFinset [Fintype G.edgeSet] [Fintype H.edgeSet] :
    Disjoint G.edgeFinset H.edgeFinset ↔ Disjoint G H := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp]
lemma edgeFinset_eq_empty [Fintype G.edgeSet] : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot, edgeFinset_inj]

@[simp]
lemma edgeFinset_nonempty [Fintype G.edgeSet] : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
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

@[simp] lemma adj_ind : (G.ind s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s := Iff.rfl

@[simp] lemma ind_empty (G : SimpleGraph α) : G.ind ∅ = ⊥ := by ext; simp
@[simp] lemma ind_univ (G : SimpleGraph α) : G.ind univ = G := by ext; simp

@[simp]
lemma ind_singleton (G : SimpleGraph α) (a : α) : G.ind {a} = ⊥ := by
  ext; simp; rintro h rfl; exact h.ne'

@[simp]
lemma ind_inter (G : SimpleGraph α) (s t : Set α) : G.ind (s ∩ t) = G.ind s ⊓ G.ind t := by
  ext; simp; tauto

/-- Induced subgraphs on disjoint sets meet in the empty graph. -/
lemma disjoint_ind (h : Disjoint s t) : Disjoint (G.ind s) (G.ind t) := by
  rw [disjoint_iff, ← ind_inter, disjoint_iff_inter_eq_empty.1 h, ind_empty]

end Ind
end SimpleGraph
