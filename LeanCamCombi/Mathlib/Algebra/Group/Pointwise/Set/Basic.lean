import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Prod
open scoped Pointwise

@[simp]
lemma Set.one_prod_one {α β : Type*} [One α] [One β] :
  (1 ×ˢ 1 : Set (α × β)) = 1 := by
  ext
  simp [Prod.ext_iff]

@[simp]
lemma Set.inv_prod {α β : Type*} [Inv α] [Inv β]
  (s : Set α) (t : Set β) :
  (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹:=
  rfl

@[simp]
lemma Set.prod_mul_prod_comm {α β : Type*} (s₁ s₂: Set α) (t₁ t₂ : Set β)
  [Mul α] [Mul β]:
  (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) := by
  ext
  simp [mem_mul]
  aesop

lemma Set.prod_pow {α β : Type*} (s : Set α) (t : Set β)
  [Monoid α] [Monoid β] : ∀ n,
  (s ×ˢ t)^n = (s^n) ×ˢ (t^n)
  | 0 => by simp
  | n+1 => by simp [pow_succ,Set.prod_pow _ _ n]
