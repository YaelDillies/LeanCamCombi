import order.hom.set

open order_dual set

section lattice
variables {α : Type*} [lattice α] [bounded_order α] {a b : α}

lemma is_compl_comm : is_compl a b ↔ is_compl b a := ⟨is_compl.symm, is_compl.symm⟩

end lattice

section boolean_algebra
variables {α : Type*} [boolean_algebra α]

@[simp] lemma order_iso.compl_symm_apply' (a : αᵒᵈ) : (order_iso.compl α).symm a = (of_dual a)ᶜ :=
rfl

end boolean_algebra
