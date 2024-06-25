import Mathlib.Algebra.Module.BigOperators

variable {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

lemma Finset.sum_smul_sum' (s : Finset α) (t : Finset β) {f : α → R} {g : β → M} :
    (∑ i ∈ s, f i) • ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i • g j := by
  simp_rw [sum_smul, ← smul_sum]
