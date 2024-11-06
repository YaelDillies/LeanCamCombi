import Mathlib.Data.Set.Lattice

namespace Set
variable {α β : Type*} {s : Set α}

@[simp] lemma biUnion_const (hs : s.Nonempty) (t : Set β) : ⋃ a ∈ s, t = t := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion, iUnion_const]

@[simp] lemma biInter_const (hs : s.Nonempty) (t : Set β) : ⋂ a ∈ s, t = t := by
  have := hs.to_subtype
  rw [biInter_eq_iInter, iInter_const]

end Set
