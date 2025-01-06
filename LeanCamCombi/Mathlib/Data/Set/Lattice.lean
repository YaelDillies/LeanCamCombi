import Mathlib.Data.Set.Lattice

section
variable {α : Type*} [CompleteLattice α]

lemma iInf_le_iSup {ι : Sort*} [Nonempty ι] {f : ι → α} : ⨅ i, f i ≤ ⨆ i, f i :=
  (iInf_le _ (Classical.arbitrary _)).trans <| le_iSup _ (Classical.arbitrary _)

lemma biInf_le_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι → α} :
    ⨅ i ∈ s, f i ≤ ⨆ i ∈ s, f i :=
  (biInf_le _ hs.choose_spec).trans <| le_biSup _ hs.choose_spec

end

namespace Set
variable {α : Type*} {s : Set α} {a : α}

lemma iInter_subset_iUnion {ι : Sort*} [Nonempty ι] {f : ι → Set α} : ⋂ i, f i ⊆ ⋃ i, f i :=
  iInf_le_iSup

lemma biInter_subset_biUnion {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι → Set α} :
    ⋂ i ∈ s, f i ⊆ ⋃ i ∈ s, f i := biInf_le_biSup hs

end Set
