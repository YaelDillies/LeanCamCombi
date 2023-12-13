import Mathlib.GroupTheory.QuotientGroup

open Set
open scoped Pointwise

variable {α : Type*}

namespace Subgroup
section Group
variable [Group α] {H : Subgroup α} [Subgroup.Normal H] {s t : Set α}

@[to_additive]
lemma image_coe_quotient (H : Subgroup α) [H.Normal] : ((↑) : α → α ⧸ H) '' H = 1 := by
  ext a
  dsimp
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [mem_one, QuotientGroup.eq_one_iff]
  · rintro rfl
    exact ⟨1, H.one_mem, rfl⟩

@[to_additive]
lemma preimage_image_coe (s : Set α) : ((↑) : α → α ⧸ H) ⁻¹' ((↑) '' s) = H * s := by
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine' ⟨a / b, b, (QuotientGroup.eq_one_iff _).1 _, hb, div_mul_cancel' _ _⟩
    simp only [h, QuotientGroup.mk_div, div_self']
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨b, hb, _⟩
    simpa only [QuotientGroup.mk_mul, self_eq_mul_left, QuotientGroup.eq_one_iff]

@[to_additive]
lemma image_coe_inj : ((↑) : α → α ⧸ H) '' s = ((↑) : α → α ⧸ H) '' t ↔ ↑H * s = H * t := by
  simp_rw [← preimage_image_coe]
  exact QuotientGroup.mk_surjective.preimage_injective.eq_iff.symm

end Group

section CommGroup
variable [CommGroup α] {s : Subgroup α} {a : α}

@[to_additive]
lemma mul_alt_version (N : Subgroup α) (s : Set α) :
    (↑) ⁻¹' (((↑) : α → α ⧸ N) '' s) = ⋃ x : N, x • s := by
  simp_rw [QuotientGroup.preimage_image_mk N s, mul_comm _ (↑(_ : N) : α), ← Set.iUnion_inv_smul, ←
    Set.preimage_smul _ s]
  congr

end CommGroup
end Subgroup
