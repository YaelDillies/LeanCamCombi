/-
Copyright (c) 2025, 2026 Yahel Manor, Jing Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yahel Manor, Jing Guo
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Slice
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Upper bound on `l`-intersecting families

This file proves an upper bound on `l`-intersecting families.

A family of sets is called `l`-intersecting if the size of the intersection of
any two sets in the family is at least `l`.

## Main results

* `IsIntersectingFamily.card_le_of_sized`: If `𝒜` is a family of `r`-subsets of a finite type
  `α`, and `𝒜` is `l`-intersecting, then `Nat.card 𝒜 ≤ ((card α) - l).choose (r - l)`.

## References

* Theorem 1.17 in the [lecture note](https://github.com/YaelDillies/maths-notes/blob/master/combinatorics.pdf)
-/

public section

open Fintype
open Finset

variable {α : Type*} [DecidableEq α]

namespace IsIntersectingFamily

/--
If `𝒜` is a `k`-intersecting family of sets, and every set in `𝒜` has size `r`,
for `r ≥ k`, then for any `A, B ∈ 𝒜`, we have `k ≤ #(A ∩ B)`.
-/
theorem le_card_inter_of_sized {k r : ℕ} {𝒜 : Set (Finset α)}
    (sized : 𝒜.Sized r) (k_le_r : k ≤ r) (inter : (Set.Ici k).IsIntersectingOf 𝒜)
    {A B : Finset α} (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) : k ≤ #(A ∩ B) := by
  rcases eq_or_ne A B with rfl | hab
  · simpa [sized hA] using k_le_r
  · exact inter hA hB hab

variable [Fintype α]

/-- Upper bound for `l`-intersecting families

Let `α` be finite and `𝒜` a family of `r`-element subsets of `α`.
If `𝒜` is `l`-intersecting and `card α` is sufficiently large,
then `Nat.card 𝒜 ≤ ((card α) - l).choose (r - l)`.
-/
theorem card_le_of_sized {l r : ℕ} {𝒜 : Set (Finset α)}
    (sized𝒜 : Set.Sized r 𝒜) (inter : (Set.Ici l).IsIntersectingOf 𝒜)
    (h_card_alpha_large : 2 ^ (3 * r) * r * r + 5 * r ≤ card α) :
  Nat.card 𝒜 ≤ ((card α) - l).choose (r - l) := by
  lift 𝒜 to Finset (Finset α) using 𝒜.toFinite
  let ℬ : Finset (Finset α) := 𝒜
  have hcard : Nat.card (↑↑ℬ : Set (Finset α)) = #ℬ := by simp
  rw [hcard]
  have sizedℬ : Set.Sized r (ℬ : Set (Finset α)) := by simpa [ℬ] using sized𝒜
  have interℬ : (Set.Ici l).IsIntersectingOf (ℬ : Set (Finset α)) := by
    simpa [ℬ] using inter
  clear inter
  obtain hℬempty | ⟨el, el_in_ℬ⟩ := ℬ.eq_empty_or_nonempty
  · rw [hℬempty]
    simp only [Finset.card_empty, zero_le]
  have r_le_card_α : r ≤ card α := by
    calc
      r = #el := by simp [sizedℬ el_in_ℬ]
      _ ≤ #((univ : Finset α)) := card_le_card (subset_univ el)
      _ = card α := by simp
  by_cases l_le_r : l ≤ r
  · induction l_le_r using Nat.decreasingInduction with
    | self =>
      simp only [tsub_self, Nat.choose_zero_right, Finset.card_le_one_iff]
      intro A B A_in_ℬ B_in_ℬ
      suffices A_cap_B_eq_A : A ∩ B = A from by
        apply eq_of_subset_of_card_le (inter_eq_left.mp A_cap_B_eq_A)
        simp [sizedℬ A_in_ℬ, sizedℬ B_in_ℬ]
      apply eq_of_subset_of_card_le inter_subset_left
      calc
        #A = r := by simp [sizedℬ A_in_ℬ]
        _ ≤ #(A ∩ B) := by
          exact le_card_inter_of_sized sizedℬ le_rfl interℬ A_in_ℬ B_in_ℬ
    | of_succ k k_leq_r ind =>
      have interℬ' : ∀ ⦃A B : Finset α⦄, A ∈ ℬ → B ∈ ℬ → k ≤ #(A ∩ B) := by
        intro A B hA hB
        exact le_card_inter_of_sized sizedℬ
          (Nat.le_of_lt k_leq_r) interℬ hA hB
      by_cases inter_succ_k : (Set.Ici (k + 1)).IsIntersectingOf (ℬ : Set (Finset α))
      · calc
        _ ≤ (card α - (k + 1)).choose (r - (k + 1)) := ind inter_succ_k
        _ = (card α - (k + 1)).choose (card α - (k + 1) - (r - (k + 1))) := by
          rw [Nat.choose_symm]; omega
        _ = (card α - (k + 1)).choose (card α - r) := by congr 1; omega
        _ = (card α - k - 1).choose (card α - r) := by congr 1
        _ ≤ (card α - k).choose (card α - r) := by apply Nat.choose_mono; omega
        _ ≤ (card α - k).choose (card α - k - (card α - r)) := by
          rw [Nat.choose_symm]; omega
        _ = (card α - k).choose (r - k) := by congr 1; omega
      have inter_succ_k' : ∃ A₁ ∈ ℬ, ∃ A₂ ∈ ℬ, A₁ ≠ A₂ ∧ #(A₁ ∩ A₂) ≤ k := by
        simpa [Set.IsIntersectingOf, Set.Pairwise, Set.mem_Ici,
          Nat.succ_le_iff, not_forall, Classical.not_imp] using inter_succ_k
      obtain ⟨A₁, A₁_in_ℬ, A₂, A₂_in_ℬ, card_x₁_x₂⟩ := inter_succ_k'
      have k_le_inter := interℬ' A₁_in_ℬ A₂_in_ℬ
      have inter_eq_k : #(A₁ ∩ A₂) = k := Eq.symm (Nat.le_antisymm k_le_inter card_x₁_x₂.2)
      by_cases s_eq_inter_all : ∃ s, k ≤ #s ∧ ∀ A ∈ ℬ, s ⊆ A
      · obtain ⟨s, _, s_inter_a⟩ := s_eq_inter_all
        have mem_univ_sdiff_of_mem_sdiff {x : α} {t : Finset α} (hx : x ∈ t \ s) :
            x ∈ univ \ s := by
          exact mem_sdiff.mpr ⟨mem_univ x, (mem_sdiff.mp hx).2⟩
        have card_map_ℬ_eq_cardℬ : #(image (· \ s) ℬ) = #ℬ := by
          refine card_image_iff.mpr ?_
          rw [Set.InjOn]
          intro x₁ x₁_in_ℬ x₂ x₂_in_ℬ x₁_sub_eq_x₂_sub
          ext a
          by_cases a_in_s : a ∈ s
          · exact (iff_true_right (s_inter_a x₂ x₂_in_ℬ a_in_s)).mpr (s_inter_a x₁ x₁_in_ℬ a_in_s)
          · have a_x_iff_a_in_mp : ∀ x ∈ ℬ, a ∈ x ↔ a ∈ ((· \ s) x) := by
              simp only [mem_sdiff, iff_self_and]
              exact fun _ _ _ => a_in_s
            rw [a_x_iff_a_in_mp x₁ x₁_in_ℬ, a_x_iff_a_in_mp x₂ x₂_in_ℬ]
            exact Eq.to_iff (congrFun (congrArg Membership.mem x₁_sub_eq_x₂_sub) a)
        have sized_map_ℬ : image (· \ s) ℬ ⊆ powersetCard (r - #s) (univ \ s) := by
          rw [subset_iff]
          intro y hy
          rcases mem_image.mp hy with ⟨x, x_in_ℬ, rfl⟩
          rw [mem_powersetCard]
          constructor
          · intro a ha
            exact mem_univ_sdiff_of_mem_sdiff ha
          · rw [card_sdiff, inter_eq_left.mpr (s_inter_a x x_in_ℬ), sizedℬ x_in_ℬ]
        rw [← card_map_ℬ_eq_cardℬ]
        apply le_trans (card_le_card sized_map_ℬ)
        simp only [card_powersetCard]
        rw [card_univ_diff s]
        rw [← (Nat.choose_symm (Nat.sub_le_sub_right r_le_card_α #s))]
        rw [← (Nat.choose_symm (Nat.sub_le_sub_right r_le_card_α k))]
        have : #s ≤ r := by
          rw [← sizedℬ el_in_ℬ]
          exact card_le_card (s_inter_a el el_in_ℬ)
        have card_sub_s_eq : card α - #s - (r - #s) = card α - r := by omega
        have card_sub_k_eq : card α - k - (r - k) = card α - r := by omega
        rw [card_sub_s_eq, card_sub_k_eq]
        refine Nat.choose_le_choose (card α - r) ?_
        omega
      push Not at s_eq_inter_all
      have ⟨A₃, A₃_in_ℬ, A₃_prop⟩ := s_eq_inter_all (A₁ ∩ A₂) k_le_inter
      have inter_lt_k : #((A₁ ∩ A₂) ∩ A₃) < k := by
        by_contra k_le_inter₃
        simp [← inter_eq_k, ← (card_inter_add_card_sdiff (A₁ ∩ A₂) A₃)] at k_le_inter₃
        trivial
      let U := A₁ ∪ A₂ ∪ A₃
      have card_U : #U ≤ 3 * r := by
        dsimp [U]
        rw [union_assoc]
        calc
          #(A₁ ∪ (A₂ ∪ A₃)) ≤ #A₁ + #(A₂ ∪ A₃) := card_union_le A₁ (A₂ ∪ A₃)
          _ ≤ #A₁ + (#A₂ + #A₃) := by gcongr; exact card_union_le ..
          _ ≤ r + (r + r) := by gcongr <;> exact Nat.le_of_eq (sizedℬ ‹_›)
          _ = 3 * r := by omega
      have : k ≤ #U := by
        calc
          k ≤ r := by omega
          _ = #A₁ := by rw [sizedℬ A₁_in_ℬ]
          _ ≤ #U := by apply card_le_card; simp [U]
      have succ_k_le_inter_a_U : ∀ a ∈ ℬ, k + 1 ≤ #(a ∩ U) := by
        by_contra! ex
        obtain ⟨a, a_in_ℬ, a_inter_le_k⟩ := ex
        have k_le_inter_U : k ≤ #(a ∩ U) := by
          calc
            k ≤ #(a ∩ A₁) := interℬ' a_in_ℬ A₁_in_ℬ
            _ ≤ #(a ∩ U) := by
              apply card_le_card
              exact inter_subset_inter_left (by simp [U])
        have card_inter_eq_k : #(a ∩ U) = k := by omega
        dsimp [U] at card_inter_eq_k
        rw [union_assoc] at card_inter_eq_k
        rw [← union_assoc, union_comm, inter_union_distrib_left, inter_union_distrib_left]
          at card_inter_eq_k
        have k_le_inter_a_A₁_A₂ : k ≤ #(a ∩ (A₁ ∩ A₂)) := by
          calc
            k ≤ k + k - k := by simp
            _ ≤ k + k - #(a ∩ (A₁ ∪ A₂)) := by
              apply Nat.sub_le_sub_left
              simp [← card_inter_eq_k, card_le_card, inter_union_distrib_left]
            _ ≤ k + k - #(a ∩ A₁ ∪ (a ∩ A₂)) := by simp [inter_union_distrib_left]
            _ ≤ #(a ∩ A₁) + #(a ∩ A₂) - #(a ∩ A₁ ∪ (a ∩ A₂)) := by
              gcongr <;> exact interℬ' a_in_ℬ ‹_›
            _ = #((a ∩ A₁) ∩ (a ∩ A₂)) := Eq.symm (card_inter (a ∩ A₁) (a ∩ A₂))
            _ = #(a ∩ (A₁ ∩ A₂)) := by
              congr 1
              exact Eq.symm (inter_inter_distrib_left a A₁ A₂)
        have k_plus_k_sub_le :
            k + k - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) ≤
              #(a ∩ A₃) + #(a ∩ (A₁ ∩ A₂)) - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) := by
          calc
            k + k - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) ≤
                k + #(a ∩ (A₁ ∩ A₂)) - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) := by
              gcongr
            _ ≤ #(a ∩ A₃) + #(a ∩ (A₁ ∩ A₂)) - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) := by
              gcongr
              exact interℬ' a_in_ℬ A₃_in_ℬ
        have k_lt_k := calc
          k = k + k - k := by simp
          _ < k + k - #((A₁ ∩ A₂) ∩ A₃) := by
            refine (tsub_lt_tsub_iff_left_of_le ?_).mpr inter_lt_k
            omega
          _ ≤ k + k - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) := by
            gcongr k + k - #?_
            nth_rw 2 [inter_comm]
            exact inter_subset_right
          _ ≤ #(a ∩ A₃) + #(a ∩ (A₁ ∩ A₂)) - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) := k_plus_k_sub_le
          _ = #(a ∩ A₃) + #(a ∩ (A₁ ∩ A₂)) - #(a ∩ A₃ ∩ (a ∩ (A₁ ∩ A₂))) := by
            congr 2
            rw [inter_inter_distrib_left]
          _ = #(a ∩ A₃ ∪ (a ∩ (A₁ ∩ A₂))) := by rw [card_union]
          _ = #(a ∩ (A₃ ∪ (A₁ ∩ A₂))) := by rw [inter_union_distrib_left]
          _ ≤ #(a ∩ U) := by
            gcongr
            change A₃ ∪ (A₁ ∩ A₂) ⊆ A₁ ∪ A₂ ∪ A₃
            intro x hx
            rcases mem_union.mp hx with hx3 | hx12
            · exact mem_union.mpr <| Or.inr hx3
            · exact mem_union.mpr <| Or.inl <| mem_union.mpr <| Or.inl <| (mem_inter.mp hx12).1
          _ ≤ k := Nat.le_of_lt_succ a_inter_le_k
        exact (Nat.lt_irrefl _ k_lt_k).elim
      have card_ℬ_leq_prod : #ℬ ≤ #U.powerset * #{p : Finset α | ∃ a ∈ ℬ, a \ U = p} := by
        let fn : Finset α → Finset α → Finset α := fun a b ↦ a ∪ b
        rw [← ((@card_image₂_iff _ _ _ _ fn U.powerset
          {p : Finset α | ∃ a ∈ ℬ, a \ U = p}).mpr ?_)]
        · apply card_le_card
          rw [subset_iff]
          intro x x_in_ℬ
          refine mem_image₂.2 ?_
          refine ⟨x ∩ U, mem_powerset.mpr inter_subset_right, x \ U, ?_, ?_⟩
          · simpa using (show ∃ a ∈ ℬ, a \ U = x \ U from ⟨x, x_in_ℬ, rfl⟩)
          · simpa [fn, union_comm] using (sdiff_union_inter x U)
        · rw [Set.InjOn]
          intro y hy z hz hyz
          rcases y with ⟨a, b⟩
          rcases z with ⟨a', b'⟩
          simp only [Set.mem_prod, mem_coe, mem_powerset, mem_filter, mem_univ, true_and] at hy hz
          rcases hy with ⟨a_in_U, x, x_in_ℬ, x_minus_U_eq_b⟩
          rcases hz with ⟨a'_in_U, x', x'_in_ℬ, x'_minus_U_eq_b'⟩
          have cup_eq : a ∪ b = a' ∪ b' := by simpa [fn] using hyz
          have inter_parts_eq : a = a' := by
            have a_cup_b_cap_u_eq_a : (a ∪ b) ∩ U = a := by
              rw [← x_minus_U_eq_b, inter_comm, inter_union_distrib_left]
              simpa
            have a'_cup_b'_cap_u_eq_a' : (a' ∪ b') ∩ U = a' := by
              rw [← x'_minus_U_eq_b', inter_comm, inter_union_distrib_left]
              simpa
            simpa [a_cup_b_cap_u_eq_a, a'_cup_b'_cap_u_eq_a'] using
              congrArg (fun t ↦ t ∩ U) cup_eq
          have sdiff_parts_eq : b = b' := by
            have a_cup_b_sdiff_u_eq_a : (a ∪ b) \ U = b := by
              rw [union_sdiff_distrib, ← x_minus_U_eq_b, (sdiff_eq_empty_iff_subset).mpr a_in_U]
              simp
            have a'_cup_b'_sdiff_u_eq_a' : (a' ∪ b') \ U = b' := by
              rw [union_sdiff_distrib, ← x'_minus_U_eq_b',
                (sdiff_eq_empty_iff_subset).mpr a'_in_U]
              simp
            simpa [a_cup_b_sdiff_u_eq_a, a'_cup_b'_sdiff_u_eq_a'] using
              congrArg (fun t ↦ t \ U) cup_eq
          exact Prod.ext inter_parts_eq sdiff_parts_eq
      have card_filt_le_choose : #(filter (fun p ↦ ∃ a ∈ ℬ, a \ U = p) univ)
        ≤ (card α - #U).choose (r - (k + 1)) * r := by
        have mem_range_of_sdiff {a : Finset α} (a_in_ℬ : a ∈ ℬ) : #(a \ U) ∈ range (r - k) := by
          rw [mem_range]
          rw [← sizedℬ a_in_ℬ, ← card_sdiff_add_card_inter a U, Nat.lt_sub_iff_add_lt]
          exact Nat.add_lt_add_left
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (succ_k_le_inter_a_U a a_in_ℬ)) #(a \ U)
        have sdiff_mem_powersetCard {a : Finset α} :
            a \ U ∈ powersetCard #(a \ U) (univ \ U) := by
          rw [mem_powersetCard]
          constructor
          · intro x hx
            exact mem_sdiff.mpr ⟨mem_univ x, (mem_sdiff.mp hx).2⟩
          · rfl
        calc
          #{p | ∃ a ∈ ℬ, a \ U = p}
            ≤ #((range (r - k)).biUnion fun n' ↦ powersetCard n' (univ \ U)) := card_le_card ?_
          _ ≤ (card α - #U).choose (r - (k + 1)) * (r - k) := ?_
          _ ≤ (card α - #U).choose (r - (k + 1)) * r := by apply Nat.mul_le_mul_left; omega
        · rw [subset_iff]
          intro p hp
          rcases mem_filter.mp hp with ⟨_, a, a_in_ℬ, rfl⟩
          refine mem_biUnion.mpr ?_
          exact ⟨#(a \ U), mem_range_of_sdiff a_in_ℬ, sdiff_mem_powersetCard⟩
        · rw [mul_comm]
          nth_rw 2 [← card_range (r - k)]
          apply card_biUnion_le_card_mul
          intro lvl lvl_in_range
          simp only [mem_range] at lvl_in_range
          rw [card_powersetCard, card_univ_diff U]
          have lvl_lt_r_sub_succ_k : lvl ≤ r - (k + 1) := by omega
          induction lvl_lt_r_sub_succ_k using Nat.decreasingInduction with
          | self => simp
          | of_succ lvl' _ ind =>
            have _ := @Nat.choose_le_succ_of_lt_half_left lvl' (card α - #U) ?_
            all_goals omega
      calc
        #ℬ ≤ #U.powerset * #(filter (fun p ↦ ∃ a ∈ ℬ, a \ U = p) univ) := card_ℬ_leq_prod
        _ ≤ 2 ^ #U * #(filter (fun p ↦ ∃ a ∈ ℬ, a \ U = p) univ) := by
          simp only [card_powerset, le_refl, U]
        _ ≤ 2 ^ #U * ((card α - #U).choose (r - (k + 1)) * r) := by
          gcongr
        _ ≤ 2 ^ #U * ((card α - k).choose (r - (k + 1)) * r) := by
          apply_rules [Nat.mul_le_mul_left, Nat.mul_le_mul_right, Nat.choose_mono,
            Nat.sub_le_sub_left]
        _ ≤ 2 ^ (3 * r) * ((card α - k).choose (r - (k + 1)) * r) := by gcongr; simp
        _ ≤ (2 ^ (3 * r) * (r * (card α - k).choose (r - (k + 1) + 1) * (r - (k + 1) + 1)) /
          (card α - k - (r - (k + 1)))) := by
          rw [Nat.le_div_iff_mul_le, mul_assoc, mul_comm ((card α - k).choose (r - (k + 1))) r,
            mul_assoc, ← Nat.choose_succ_right_eq, mul_assoc]
          omega
        _ = (2 ^ (3 * r) * (r * (card α - k).choose (r - k) * (r - k)) /
          (card α - k - (r - (k + 1)))) := by congr <;> omega
        _ ≤ ((card α - k).choose (r - k) * (r - k) * (2 ^ (3 * r) * r) /
          (card α - k - (r - (k + 1)))) := by
          simp [← mul_assoc, mul_comm]
        _ ≤ (card α - k).choose (r - k) := ?_
      apply Nat.div_le_of_le_mul
      nth_rw 5 [mul_comm]
      nth_rw 1 [mul_assoc]
      refine Nat.mul_le_mul_left ((card α - k).choose (r - k)) ?_
      rw [Nat.le_sub_iff_add_le, Nat.le_sub_iff_add_le, add_assoc]
      · calc
        (r - k) * (2 ^ (3 * r) * r) + (r - (k + 1) + k) ≤ r * (2 ^ (3 * r) * r) + r := by
          gcongr <;> omega
        _ = 2 ^ (3 * r) * r * r + r := by simp [mul_comm]
        _ ≤ card α := by omega
      all_goals omega
  · have card_ℬ_le_one : #ℬ ≤ 1 := by
      refine card_le_one_iff.mpr ?_
      intro a b a_in_ℬ b_in_ℬ
      by_contra hab
      have l_le_inter : l ≤ #(a ∩ b) := interℬ a_in_ℬ b_in_ℬ hab
      have inter_le_r : #(a ∩ b) ≤ r := by
        calc
          #(a ∩ b) ≤ #a := card_le_card inter_subset_left
          _ = r := sizedℬ a_in_ℬ
      exact l_le_r (l_le_inter.trans inter_le_r)
    calc
      #ℬ ≤ 1 := card_ℬ_le_one
      _ ≤ ((card α) - l).choose (r - l) := by
        have r_lt_l : r < l := Nat.lt_of_not_ge l_le_r
        simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt r_lt_l)]

end IsIntersectingFamily
