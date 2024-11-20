import Mathlib.Data.Set.Pointwise.Interval

open scoped Pointwise

namespace Set
variable {α : Type*} [OrderedCommGroup α]

@[to_additive (attr := simp)]
lemma inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹ := by ext; simp [le_inv', inv_le', and_comm]

end Set

namespace Set
variable {α : Type*} [LinearOrderedCommMonoid α] [MulLeftReflectLE α] [ExistsMulOfLE α]
  {a b c d : α}

@[to_additive (attr := simp)]
lemma smul_Icc (a b c : α) : a • Icc b c = Icc (a * b) (a * c) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hby, hyc⟩, rfl⟩
    exact ⟨mul_le_mul_left' hby _, mul_le_mul_left' hyc _⟩
  · rintro ⟨habx, hxac⟩
    obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le habx
    refine ⟨b * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxac

@[to_additive]
lemma Icc_mul_Icc (hab : a ≤ b) (hcd : c ≤ d) : Icc a b * Icc c d = Icc (a * c) (b * d) := by
  refine (Icc_mul_Icc_subset' _ _ _ _).antisymm fun x ⟨hacx, hxbd⟩ ↦ ?_
  obtain hxbc | hbcx := le_total x (b * c)
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hacx
    refine ⟨a * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, c, left_mem_Icc.2 hcd, mul_right_comm ..⟩
    rwa [mul_right_comm, mul_le_mul_iff_right] at hxbc
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hbcx
    refine ⟨b, right_mem_Icc.2 hab, c * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxbd

end Set
