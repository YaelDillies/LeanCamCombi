import Mathlib.Combinatorics.SimpleGraph.Maps
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Basic

variable {α : Type*}

namespace SimpleGraph
section Ind

@[simp] lemma spanningCoe_induce (G : SimpleGraph α) (s : Set α) :
    spanningCoe (induce (s : Set α) G) = G.ind s := by ext; simp [← and_assoc]

end Ind
end SimpleGraph
