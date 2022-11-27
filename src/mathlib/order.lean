import order.bounded_order

section
variables {α : Type*} [lattice α] [bounded_order α] {a b : α}

lemma is_compl_comm : is_compl a b ↔ is_compl b a := ⟨is_compl.symm, is_compl.symm⟩

end

section
variables {α : Type*} [partial_order α] {f : α → α → α}

lemma assoc_of_comm_of_le (hf : ∀ a b, f a b = f b a) (h : ∀ a b c, f (f a b) c ≤ f a (f b c)) :
  ∀ a b c, f (f a b) c = f a (f b c) :=
λ a b c, le_antisymm (h _ _ _) $ by { rw [hf, hf b, hf _ c, hf a], exact h _ _ _ }

end
