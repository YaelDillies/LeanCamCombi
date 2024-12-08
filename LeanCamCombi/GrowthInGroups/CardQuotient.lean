import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.GroupTheory.QuotientGroup.Defs

open Finset Function
open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {H : Subgroup G} [DecidablePred (· ∈ H)] [H.Normal]
  {A : Finset G} {m n : ℕ}

@[to_additive]
lemma card_pow_quotient_mul_pow_inter_subgroup :
    #((A ^ m).image <| QuotientGroup.mk' H) * #{x ∈ A ^ n | x ∈ H} ≤ #(A ^ (m + n)) := by
  set π := QuotientGroup.mk' H
  let φ := invFunOn π (A ^ m)
  have hφ : Set.InjOn φ (π '' (A ^ m)) := invFunOn_injOn_image ..
  have hφA {a} (ha : a ∈ π '' (A ^ m)) : φ a ∈ A ^ m := by
    have := invFunOn_mem (by simpa using ha)
    norm_cast at this
    simpa using this
  have hπφ {a} (ha : a ∈ π '' (A ^ m)) : π (φ a) = a := invFunOn_eq (by simpa using ha)
  calc
    #((A ^ m).image π) * #{x ∈ A ^ n | x ∈ H}
    _ = #(((A ^ m).image π).image φ) * #{x ∈ A ^ n | x ∈ H} := by
      rw [Finset.card_image_of_injOn (f := φ) (mod_cast hφ)]
    _ ≤ #(((A ^ m).image π).image φ * {x ∈ A ^ n | x ∈ H}) := by
      rw [Finset.card_mul_iff.2]
      simp only [Set.InjOn, coe_image, coe_pow, coe_filter, Set.mem_prod, Set.mem_image,
        exists_exists_and_eq_and, Set.mem_setOf_eq, and_imp, forall_exists_index, Prod.forall,
        Prod.mk.injEq]
      rintro _ a₁ b₁ hb₁ rfl - ha₁ _ a₂ b₂ hb₂ rfl - ha₂ hab
      have := hπφ <| Set.mem_image_of_mem _ hb₁
      have hπa₁ : π a₁ = 1 := (QuotientGroup.eq_one_iff _).2 ha₁
      have hπa₂ : π a₂ = 1 := (QuotientGroup.eq_one_iff _).2 ha₂
      have hπb : π b₁ = π b₂ := by
        simpa [hπφ, Set.mem_image_of_mem π, hb₁, hb₂, hπa₁, hπa₂] using congr(π $hab)
      aesop
    _ ≤ #(A ^ (m + n)) := by
      gcongr
      simp only [mul_subset_iff, mem_image, exists_exists_and_eq_and, Finset.mem_filter, and_imp,
        forall_exists_index, forall_apply_eq_imp_iff₂, pow_add]
      rintro a ha b hb -
      exact mul_mem_mul (hφA <| Set.mem_image_of_mem _ <| mod_cast ha) hb

@[to_additive]
lemma le_card_quotient_mul_sq_inter_subgroup (hAsymm : A⁻¹ = A) :
    #A ≤ #(A.image <| QuotientGroup.mk' H) * #{x ∈ A ^ 2 | x ∈ H} := by
  classical
  set π := QuotientGroup.mk' H
  calc
    #A = #A * 1 := by rw [mul_one]
    _ ≤ #(A.image π) * #{x ∈ A ^ 2 | x ∈ H} :=
      card_mul_le_card_mul (π · = ·) (by simp [Finset.Nonempty]; aesop) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rintro a ha
  calc
    #(bipartiteBelow (π · = ·) A (π a))
    _ ≤ #((bipartiteBelow (π · = ·) A (π a))⁻¹ * (bipartiteBelow (π · = ·) A (π a))) :=
      card_le_card_mul_left ⟨a⁻¹, by simpa⟩
    _ ≤ #{x ∈ A⁻¹ * A | x ∈ H} := by
      gcongr
      simp only [mul_subset_iff, mem_inv', mem_bipartiteBelow, map_inv, Finset.mem_filter, and_imp]
      rintro x hx hxa y hy hya
      refine ⟨mul_mem_mul (by simpa) hy, (QuotientGroup.eq_one_iff _).1 (?_ : π _ = _)⟩
      simp [hya, ← hxa]
    _ = #{x ∈ A ^ 2 | x ∈ H} := by simp [hAsymm, sq]

end Finset
