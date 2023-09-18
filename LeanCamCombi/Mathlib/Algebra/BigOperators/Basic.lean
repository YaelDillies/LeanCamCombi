import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Powerset

-- TODO: Fix implicitness of `Finset.sum_singleton`

open scoped BigOperators

namespace Finset
variable {α β : Type*} [AddCommMonoid β]

/-- A sum over `powersetLen` which only depends on the size of the sets is constant. -/
lemma sum_powersetLen (n : ℕ) (s : Finset α) (f : ℕ → β) :
    ∑ t in powersetLen n s, f t.card = s.card.choose n • f n := by
  rw [sum_eq_card_nsmul, card_powersetLen]; rintro a ha; rw [(mem_powersetLen.1 ha).2]

end Finset
