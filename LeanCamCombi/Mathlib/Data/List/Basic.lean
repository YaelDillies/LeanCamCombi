import Mathlib.Data.List.Basic

namespace List
variable {α : Type*} {l l' l₀ l₁ l₂ : List α} {a b : α} {m n : ℕ}

lemma getLast_filter {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (hlp : l.filter p ≠ []), p (l.getLast (hlp <| ·.symm ▸ rfl)) = true →
      (l.filter p).getLast hlp = l.getLast (hlp <| ·.symm ▸ rfl)
  | [a], h, h' => by rw [List.getLast_singleton'] at h'; simp [List.filter_cons, h']
  | a :: b :: as, h, h' => by
    rw [List.getLast_cons_cons] at h' ⊢
    simp only [List.filter_cons (x := a)] at h ⊢
    obtain ha | ha := Bool.eq_false_or_eq_true (p a)
    · simp only [ha, ite_true]
      rw [getLast_cons, getLast_filter (b :: as) _ h']
      exact ne_nil_of_mem $ mem_filter.2 ⟨getLast_mem _, h'⟩
    · simp only [ha, cond_false] at h ⊢
      exact getLast_filter (b :: as) h h'

lemma cons_sublist_cons_iff' : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂ := by
  constructor
  · rintro (_ | _)
    · exact Or.inl ‹_›
    · exact Or.inr ⟨rfl, ‹_›⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact sublist_cons_of_sublist _ h
    · rwa [cons_sublist_cons_iff]

attribute [simp] nil_subperm

lemma subperm_cons_self : l <+~ a :: l := ⟨l, Perm.refl _, sublist_cons _ _⟩

@[simp] lemma subperm_nil : l <+~ [] ↔ l = [] :=
  ⟨fun h ↦ length_eq_zero.1 $ le_bot_iff.1 h.length_le, by rintro rfl; rfl⟩

end List
