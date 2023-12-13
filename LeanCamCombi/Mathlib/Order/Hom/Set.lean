import Mathlib.Order.Hom.Set

open OrderDual

section BooleanAlgebra
variable {α : Type*} [BooleanAlgebra α]

@[simp] lemma OrderIso.compl_symm_apply' (a : αᵒᵈ) : (OrderIso.compl α).symm a = ofDual aᶜ := rfl

end BooleanAlgebra
