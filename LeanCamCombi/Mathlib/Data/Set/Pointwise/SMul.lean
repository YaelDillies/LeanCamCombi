import Mathlib.Data.Set.Pointwise.SMul

open MulOpposite
open scoped Pointwise

namespace Set
variable {α β : Type*}

section Mul
variable [Mul α] {s t : Set α} {a : α}

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Set α) : {a} * s = a • s := singleton_mul

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Set α) (a : α) : s * {a} = op a • s := mul_singleton

end Mul
end Set

namespace Set
variable {α β : Type*}

section Group
variable [Group α] [MulAction α β] {s : Set β} {t : Set β} {a : α}

-- TODO: Replace
@[to_additive (attr := simp)]
lemma smul_set_subset_smul_set_iff : a • s ⊆ a • t ↔ s ⊆ t := set_smul_subset_set_smul_iff

end Group
end Set
