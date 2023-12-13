import Mathlib.Data.Finset.Pointwise

open MulOpposite
open scoped Pointwise

attribute [simp] Finset.zero_smul_finset

variable {α : Type*} {s : Set ℕ}

instance Nat.decidablePred_mem_vadd [DecidablePred (· ∈ s)] (a : ℕ) : DecidablePred (· ∈ a +ᵥ s) :=
  fun n ↦ decidable_of_iff' (a ≤ n ∧ n - a ∈ s) $ by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop

namespace Finset
section One
variable [One α] {s : Finset α}

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

end One

section Mul
variable [DecidableEq α] [Mul α]

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Finset α) : {a} * s = a • s := singleton_mul _

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Finset α) (a : α) : s * {a} = op a • s := mul_singleton _

end Mul

section InvolutiveInv
variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

@[to_additive (attr := simp)]
lemma mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [mem_inv, inv_eq_iff_eq_inv]

end InvolutiveInv

section Group
variable [DecidableEq α] [Group α]

@[to_additive (attr := simp)]
lemma inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

@[to_additive (attr := simp)]
lemma inv_op_smul_finset_distrib (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

end Group

section GroupWithZero
variable [DecidableEq α] [GroupWithZero α]

@[simp] protected lemma inv_zero : (0 : Finset α)⁻¹ = 0 := by ext; simp

@[simp] lemma inv_smul_set_distrib₀ (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [← inv_smul_mem_iff₀, *]

@[simp] lemma inv_op_smul_set_distrib₀ (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [← inv_smul_mem_iff₀, *]

end GroupWithZero
end Finset
