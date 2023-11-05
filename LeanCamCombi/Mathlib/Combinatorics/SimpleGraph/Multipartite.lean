import Mathlib.Combinatorics.SimpleGraph.Basic
import LeanCamCombi.Mathlib.Order.Partition.Finpartition

open Finset

namespace Finpartition
variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  {s t : Finset α} {a b : α}

@[simps]
def multipartiteGraph (P : Finpartition (univ : Finset α)) : SimpleGraph α
    where
  Adj a b := ∀ ⦃s⦄, s ∈ P.parts → a ∈ s → b ∉ s
  symm a b hab := by simpa only [imp_not_comm] using hab
  loopless a ha := by obtain ⟨s, hs, has⟩ := P.exists_mem (mem_univ a); exact ha hs has has

instance : DecidableRel (multipartiteGraph P).Adj := fun _ _ => Finset.decidableDforallFinset

/-- If v and w are in distinct parts then they are adjacent. -/
lemma multipartiteGraph_adj_of_mem_parts (hs : s ∈ P.parts) (ht : t ∈ P.parts) (ha : a ∈ s)
    (hb : b ∈ t) : (multipartiteGraph P).Adj a b ↔ s ≠ t := by
  refine' ⟨_, fun hst u hu hau hbu => hst _⟩
  · rintro hab rfl
    exact hab hs ha hb
  · rw [P.eq_of_mem_parts hs hu ha hau, P.eq_of_mem_parts ht hu hb hbu]

end Finpartition
