import Mathlib.Algebra.Group.Subgroup.Pointwise
import LeanCamCombi.Mathlib.Algebra.Group.Subgroup.Lattice

open Set Subgroup
open scoped Pointwise

namespace Subgroup
variable {G : Type*} [Group G] {s : Set G} {n : ℕ}

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

end Subgroup
