import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise

namespace Set
variable {α : Type*}

section CommMonoid
variable [CommMonoid α] {n : ℕ}

@[to_additive]
lemma mem_pow_iff_prod :
    ∀ {n} {s : Set α} {a : α}, a ∈ s ^ n ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ ∏ i, f i = a
  | 0, s, a => by simp [eq_comm]
  | n + 1, s, a => by
    rw [(Fin.consEquiv _).symm.exists_congr_left]
    simp only [pow_succ, mem_mul, mem_pow_iff_prod, exists_exists_and_eq_and, Equiv.symm_symm,
      Fin.consEquiv_apply, Fin.forall_iff_succ, Fin.cons_zero, Fin.cons_succ, Prod.exists,
      Fin.prod_univ_succ]
    constructor
    · rintro ⟨f, hf, b, hb, rfl⟩
      exact ⟨b, f, ⟨hb, hf⟩, mul_comm ..⟩
    · rintro ⟨b, f, ⟨hb, hf⟩, rfl⟩
      exact ⟨f, hf, b, hb, mul_comm ..⟩

end CommMonoid
end Set
