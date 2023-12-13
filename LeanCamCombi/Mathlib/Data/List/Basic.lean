import Mathlib.Data.List.Basic

namespace List

lemma getLast_filter {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (hlp : l.filter p ≠ []), p (l.getLast (hlp <| ·.symm ▸ rfl)) = true →
      (l.filter p).getLast hlp = l.getLast (hlp <| ·.symm ▸ rfl)
  | [a], h, h' => by rw [List.getLast_singleton'] at h'; simp [List.filter_cons, h']
  | (a :: b :: as), h, h' => by
      rw [List.getLast_cons_cons] at h' ⊢
      simp only [List.filter_cons (x := a)] at h ⊢
      rcases Bool.eq_false_or_eq_true (p a) with ha | ha
      · simp only [ha, ite_true]
        have : (b :: as).filter p ≠ []
        · have : (b :: as).getLast (List.cons_ne_nil _ _) ∈ (b :: as).filter p
          · rw [List.mem_filter]
            exact ⟨List.getLast_mem _, h'⟩
          exact List.ne_nil_of_mem this
        rw [List.getLast_cons this, getLast_filter (b :: as) this h']
      simp only [ha, cond_false] at h ⊢
      exact getLast_filter (b :: as) h h'

end List
