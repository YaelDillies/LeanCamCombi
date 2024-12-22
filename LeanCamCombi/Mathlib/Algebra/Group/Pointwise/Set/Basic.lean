import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Prod

open scoped Pointwise

namespace Set
variable {α β : Type*}

@[to_additive (attr := simp)]
lemma one_prod_one [One α] [One β] : (1 ×ˢ 1 : Set (α × β)) = 1 := by ext; simp [Prod.ext_iff]

@[to_additive (attr := simp)]
lemma inv_prod [Inv α] [Inv β] (s : Set α) (t : Set β) : (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹:= rfl

@[to_additive (attr := simp)]
lemma prod_mul_prod_comm [Mul α] [Mul β] (s₁ s₂: Set α) (t₁ t₂ : Set β) :
   (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) := by ext; simp [mem_mul]; aesop

@[to_additive]
lemma prod_pow [Monoid α] [Monoid β] (s : Set α) (t : Set β) :
    ∀ n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
  | 0 => by simp
  | n+1 => by simp [pow_succ, prod_pow _ _ n]

end Set
