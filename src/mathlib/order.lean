import order.disjoint

section
variables {α : Type*} [lattice α] [bounded_order α] {a b : α}

lemma is_compl_comm : is_compl a b ↔ is_compl b a := ⟨is_compl.symm, is_compl.symm⟩

end
