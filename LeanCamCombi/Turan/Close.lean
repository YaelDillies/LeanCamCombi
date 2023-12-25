import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset Nat

namespace SimpleGraph

variable {α : Type _} {G H : SimpleGraph α} {m n : ℕ}

-- main new def below "G.is_close H s" if by deleting at most s edges from G we obtain a subgraph of H
-- G.is_close s H iff there exists a finset of at most s edges such that G-S is a subgraph of H
def IsClose (G H : SimpleGraph α) (n : ℕ) : Prop :=
  ∃ s : Finset (Sym2 α), G.deleteEdges s ≤ H ∧ s.card ≤ n

theorem isClose_refl (G : SimpleGraph α) (n : ℕ) : G.IsClose G n :=
  ⟨∅, deleteEdges_le _ _, zero_le _⟩

theorem isClose_rfl : G.IsClose G n :=
  isClose_refl _ _

theorem IsClose.mono (h : m ≤ n) : G.IsClose H m → G.IsClose H n :=
  Exists.imp fun s => And.imp_right h.trans'

theorem isClose_trivial [Fintype G.edgeSetEmbedding] (H : SimpleGraph α)
    (h : G.edgeFinset.card ≤ n) : G.IsClose H n :=
  ⟨G.edgeFinset, by simp, h⟩

end SimpleGraph
