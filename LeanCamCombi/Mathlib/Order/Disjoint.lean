import Mathlib.Order.Disjoint

section Lattice
variable {α : Type*} [Lattice α] [BoundedOrder α] {a b : α}

lemma isCompl_comm : IsCompl a b ↔ IsCompl b a := ⟨IsCompl.symm, IsCompl.symm⟩

end Lattice
