import Mathlib.Algebra.Group.Submonoid.Pointwise
import LeanCamCombi.Mathlib.Algebra.Group.Submonoid.Basic

open Set
open scoped Pointwise

variable {α : Type*} {G : Type*} {M : Type*} {R : Type*} {A : Type*}
variable [Monoid M] [AddMonoid A]

namespace Submonoid
variable {s : Set M} {n : ℕ}

@[to_additive]
lemma closure_pow_le : ∀ {n}, n ≠ 0 → closure (s ^ n) ≤ closure s
  | 1, _ => by simp
  | n + 2, _ =>
    calc
      closure (s ^ (n + 2))
      _ = closure (s ^ (n + 1) * s) := by rw [pow_succ]
      _ ≤ closure (s ^ (n + 1)) ⊔ closure s := closure_mul_le ..
      _ ≤ closure s ⊔ closure s := by gcongr ?_ ⊔ _; exact closure_pow_le n.succ_ne_zero
      _ = closure s := sup_idem _

@[to_additive]
lemma closure_pow (hs : 1 ∈ s) (hn : n ≠ 0) : closure (s ^ n) = closure s :=
  (closure_pow_le hn).antisymm <| by gcongr; exact subset_pow hs hn

end Submonoid
