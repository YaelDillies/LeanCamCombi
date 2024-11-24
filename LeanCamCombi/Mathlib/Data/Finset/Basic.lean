import Mathlib.Data.Finset.Basic

namespace Finset
variable {α : Type*} {a : α} {s t : Finset α}

lemma not_mem_subset (h : s ⊆ t) : a ∉ t → a ∉ s := Set.not_mem_subset h

end Finset

namespace Finset
variable {ι α : Type*} [DecidableEq α] {s : Set ι} {f : ι → Finset α}

lemma pairwiseDisjoint_iff :
    s.PairwiseDisjoint f ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

end Finset
