import Mathlib.Order.Hom.Set

open OrderDual Set

section Lattice
variable {α : Type _} [Lattice α] [BoundedOrder α] {a b : α}

lemma isCompl_comm : IsCompl a b ↔ IsCompl b a :=
  ⟨IsCompl.symm, IsCompl.symm⟩

end Lattice

section BooleanAlgebra
variable {α : Type _} [BooleanAlgebra α]

@[simp]
lemma OrderIso.compl_symm_apply' (a : αᵒᵈ) : (OrderIso.compl α).symm a = ofDual aᶜ := rfl

end BooleanAlgebra
