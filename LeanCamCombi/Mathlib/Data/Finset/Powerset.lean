import Mathlib.Data.Finset.Powerset
import LeanCamCombi.Mathlib.Data.Finset.Basic
import LeanCamCombi.Mathlib.Data.Set.Pairwise.Lattice

namespace Finset
variable {α : Type*} [DecidableEq α] {s : Finset α} {a : α}

lemma pairwiseDisjoint_pair_insert (ha : a ∉ s) :
    (s.powerset : Set (Finset α)).PairwiseDisjoint
      fun t ↦ ({t, insert a t} : Set (Finset α)) := by
  simp_rw [Set.pairwiseDisjoint_iff, mem_coe, mem_powerset]
  rintro i hi j hj
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, or_imp, imp_self, true_and]
  refine ⟨?_, ?_, insert_erase_invOn.2.injOn (not_mem_mono hi ha) (not_mem_mono hj ha)⟩ <;>
    rintro rfl <;>
    cases Finset.not_mem_subset ‹_› ha (Finset.mem_insert_self _ _)

end Finset
