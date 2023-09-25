import Mathlib.Data.Set.Prod

namespace Set
variable {α β : Type*} [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}

@[simp] lemma prod_eq_univ : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]

end Set
