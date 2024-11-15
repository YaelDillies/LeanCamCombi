import Mathlib.Algebra.Group.Subgroup.Pointwise

open Subgroup
open scoped Pointwise

namespace Set
variable {G : Type*} [Group G] {s : Set G}

@[simp]
lemma mul_subgroupClosure (hs : s.Nonempty) : s * closure s = closure s := by
  rw [← smul_eq_mul, ← Set.iUnion_smul_set]
  have h a (ha : a ∈ s) : a • (closure s : Set G) = closure s :=
    smul_coe_set <| subset_closure ha
  simp (config := {contextual := true}) [h, hs]

@[simp]
lemma mul_subgroupClosure_pow (hs : s.Nonempty) : ∀ n, s ^ n * closure s = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_add, pow_one, mul_assoc, mul_subgroupClosure hs, mul_subgroupClosure_pow hs]

end Set
