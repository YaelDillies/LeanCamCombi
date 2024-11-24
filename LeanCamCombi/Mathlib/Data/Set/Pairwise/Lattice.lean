import Mathlib.Data.Set.Pairwise.Lattice
import LeanCamCombi.Mathlib.Data.Set.Basic

namespace Set
variable {ι α : Type*} {s : Set ι} {f : ι → Set α}

lemma pairwiseDisjoint_iff :
    s.PairwiseDisjoint f ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

end Set

namespace Set
variable {α : Type*} {s : Set α} {a : α}

lemma pairwiseDisjoint_pair_insert (ha : a ∉ s) :
    s.powerset.PairwiseDisjoint fun t ↦ ({t, insert a t} : Set (Set α)) := by
  rw [pairwiseDisjoint_iff]
  rintro i hi j hj
  have := insert_erase_invOn.2.injOn (not_mem_subset hi ha) (not_mem_subset hj ha)
  aesop (add simp [Set.Nonempty, Set.subset_def])

end Set
