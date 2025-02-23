/-
Copyright (c) 2025 Yahel Manor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yahel Manor
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Slice

/-!

# Upper bound on `l`-intersecting families

This file define `l`-intersecting families and prove a bound on their size.

A family is said to be `l`-intersecting if every two sets in the family have intersection of size at
least `l`.

## Main declaration

* `intersectingFamliy`: `intersectingFamliy l A` means that every two elements have intersection of
size at least l.

## Main statements

*  `IsIntersectingFamily.card_le_of_sized`: A intersecting family whose underlaying set is of size `n` and if all the sets in the family are of size
`l` then the size of the family is at most `(n-l).choose (r-l)` if `n` is suffintly large.

-/

namespace Finset

variable {α : Type*} [DecidableEq α]

def IsIntersectingFamily (l:ℕ) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, l ≤ (a ∩ b).card

theorem IsIntersectingFamily.le_of_sized {l r:ℕ} {𝒜 : Finset (Finset α)} (sized : @Set.Sized α r 𝒜)
  {inter : IsIntersectingFamily l 𝒜} (nonempty: Nonempty 𝒜) : l≤r := by
    obtain ⟨x,x_in_𝒜⟩ := nonempty
    rw [←sized x_in_𝒜,←(inter_self x)]
    exact inter x x_in_𝒜 x x_in_𝒜

variable [Fintype α]

theorem  IsIntersectingFamily.card_le_of_sized {l r:ℕ} {𝒜 : Finset (Finset α)} (sized𝒜 : @Set.Sized α r 𝒜)
 (inter : IsIntersectingFamily l 𝒜) (n_much_bigger_r :2 ^ (3 * r) * r * r+ 5 * r ≤ Fintype.card α):
 #𝒜 ≤ ((Fintype.card α)-l).choose (r-l) := by
    obtain rfl | ⟨el,el_in_𝒜⟩ := 𝒜.eq_empty_or_nonempty
    . simp only [card_empty, zero_le]
    have l_le_r := inter.le_of_sized sized𝒜 (Nonempty.intro ⟨el, el_in_𝒜⟩)
    simp [Set.Sized] at sized𝒜
    have r_le_card_α := card_le_card (subset_univ el)
    rw [sized𝒜 el_in_𝒜,card_univ] at r_le_card_α
    induction l_le_r using Nat.decreasingInduction with
    | self =>
      simp only [tsub_self, Nat.choose_zero_right, ge_iff_le,card_le_one_iff]
      intro a b a_in_𝒜 b_in_𝒜
      suffices a_cap_b_eq_a : a ∩ b = a from by
        apply eq_of_subset_of_card_le (inter_eq_left.mp a_cap_b_eq_a)
        simp [(sized𝒜 a_in_𝒜),(sized𝒜 b_in_𝒜)]
      simp [(eq_of_subset_of_card_le inter_subset_left),(sized𝒜 a_in_𝒜),(sized𝒜 b_in_𝒜),
        (inter a a_in_𝒜 b b_in_𝒜)]
    | of_succ k k_leq_r ind =>
      by_cases inter_succ_k : IsIntersectingFamily (k + 1) 𝒜
      . calc
        _ ≤ (Fintype.card α - (k + 1)).choose (r - (k + 1)) := ind inter_succ_k
        _ = (Fintype.card α - (k + 1)).choose (Fintype.card α - (k + 1) - (r - (k + 1))) := by
          rw [Nat.choose_symm];omega
        _ = (Fintype.card α - (k + 1)).choose (Fintype.card α - r) := by congr 1;omega
        _ = (Fintype.card α - k - 1).choose (Fintype.card α - r) := by congr 1
        _ ≤ (Fintype.card α - k).choose (Fintype.card α - r) := by apply Nat.choose_mono;omega
        _ ≤ (Fintype.card α - k).choose ((Fintype.card α - k) - (Fintype.card α - r)) := by
          rw [Nat.choose_symm];omega
        _ = (Fintype.card α - k).choose (r - k) := by congr 1; omega
      simp [IsIntersectingFamily] at inter_succ_k
      obtain ⟨A₁,A₁_in_𝒜,A₂,A₂_in_𝒜,card_x₁_x₂⟩ := inter_succ_k
      have k_le_inter := inter A₁ A₁_in_𝒜 A₂ A₂_in_𝒜
      have inter_eq_k : #(A₁ ∩ A₂) = k :=
        Eq.symm (Nat.le_antisymm (inter A₁ A₁_in_𝒜 A₂ A₂_in_𝒜) (Nat.lt_succ.mp card_x₁_x₂))
      by_cases s_eq_inter_all : ∃ s , (k ≤ #s) ∧ (∀a∈𝒜, s ⊆ a)
      . obtain ⟨s,_,s_inter_a⟩ := s_eq_inter_all
        have card𝒜_eq_cardℬ : #(image (·\s) 𝒜) = #𝒜 := by
          refine card_image_iff.mpr ?_
          simp [Set.InjOn]
          intro x₁ x₁_in_𝒜 x₂ x₂_in_𝒜 x₁_sub_eq_x₂_sub
          ext a
          by_cases a_in_s:a∈s
          . exact (iff_true_right (s_inter_a x₂ x₂_in_𝒜 a_in_s)).mpr (s_inter_a x₁ x₁_in_𝒜 a_in_s)
          . have a_x_iff_a_in_mp : ∀ x∈𝒜, a∈x ↔ a ∈ ((·\s) x) := by
              simp only [mem_sdiff, iff_self_and]
              exact fun x a_1 a ↦ a_in_s
            rw [(a_x_iff_a_in_mp x₁ x₁_in_𝒜),(a_x_iff_a_in_mp x₂ x₂_in_𝒜)]
            exact Eq.to_iff (congrFun (congrArg Membership.mem x₁_sub_eq_x₂_sub) a)
        have sized_ℬ : (image (·\s) 𝒜) ⊆ powersetCard (r-#s) (univ\s) := by
          simp [powersetCard,subset_iff]
          intro x x_in_𝒜
          exists ((·\s) x).1
          simp only [card_val, exists_prop, and_true]
          constructor
          simp only [sdiff_val]
          refine Multiset.sub_le_sub_right ?_
          simp
          rw [card_sdiff]
          exact congrFun (congrArg HSub.hSub (sized𝒜 x_in_𝒜)) #s
          exact s_inter_a x x_in_𝒜
        rw [←card𝒜_eq_cardℬ]
        apply le_trans (card_le_card sized_ℬ)
        simp [card_sdiff]
        rw [←Nat.choose_symm]
        nth_rw 2 [←Nat.choose_symm]
        have _ : #s ≤ r := by
          rw [←(sized𝒜 el_in_𝒜)]
          exact card_le_card (s_inter_a el el_in_𝒜)
        have α_sub_s_sub_r_sub_s_ : Fintype.card α - #s - (r - #s) = Fintype.card α - r := by omega
        have α_sub_k_sub_r_sub_k_ : Fintype.card α - k - (r - k) = Fintype.card α - r := by omega
        rw [α_sub_s_sub_r_sub_s_,α_sub_k_sub_r_sub_k_]
        refine Nat.choose_le_choose (Fintype.card α - r) ?_
        all_goals omega
      simp at s_eq_inter_all
      have ⟨A₃,A₃_in_𝒜,A₃_prop⟩  := s_eq_inter_all (A₁ ∩ A₂) k_le_inter
      have inter_lt_k : #((A₁ ∩ A₂) ∩ A₃) < k := by
        by_contra k_le_inter₃
        simp [not_lt,←inter_eq_k,←(card_inter_add_card_sdiff (A₁ ∩ A₂) A₃)] at k_le_inter₃
        trivial
      let U := A₁ ∪ A₂ ∪ A₃
      have card_U : #U ≤ 3 * r := by
        simp [U]
        calc
        #(A₁ ∪ (A₂ ∪ A₃)) ≤ #(A₁) + #(A₂ ∪ A₃) := card_union_le A₁ (A₂ ∪ A₃)
        _ ≤#(A₁) + (#(A₂) + #(A₃))  :=  Nat.add_le_add_left (card_union_le A₂ A₃) _
        _ ≤ r + (#(A₂) + #(A₃)) :=
          Nat.le_of_eq (congrFun (congrArg HAdd.hAdd (sized𝒜 A₁_in_𝒜)) (#A₂ + #A₃))
        _ ≤ r + (r + #(A₃)) :=
          Nat.le_of_eq (congrArg (HAdd.hAdd r) (congrFun (congrArg HAdd.hAdd (sized𝒜 A₂_in_𝒜)) #A₃))
        _ ≤ r + (r + r) :=
          Nat.le_of_eq (congrArg (HAdd.hAdd r) (congrArg (HAdd.hAdd r) (sized𝒜 A₃_in_𝒜)))
        _ ≤ 3 * r := by omega
      have _ : k ≤ #U := by
        calc
          k ≤ r := by omega
          _ = #A₁ := by rw [sized𝒜 A₁_in_𝒜]
          _ ≤ #U := by apply card_le_card;simp [U]
      have succ_k_le_inter_a_U : ∀ a ∈ 𝒜 , k + 1 ≤ #(a∩U) := by
        by_contra ex
        simp at ex
        obtain ⟨a,a_in_𝒜,a_inter_le_k⟩ := ex
        have k_le_inter_U : k ≤ #(a ∩ U) := by calc
          k ≤ #(a ∩ A₁) := inter a a_in_𝒜 A₁ A₁_in_𝒜
          _ ≤ #(a ∩ U) := by
            apply card_le_card
            simp [U,inter_subset_inter]
        have card_inter_eq_k : #(a ∩ U) = k := by omega
        simp [U] at card_inter_eq_k
        rw [←union_assoc,union_comm,inter_union_distrib_left,inter_union_distrib_left]
          at card_inter_eq_k
        have _ := calc
          k ≤ k + k - k := by simp
          _ ≤ k + k - #(a ∩ (A₁ ∪ A₂)) := by
            apply Nat.sub_le_sub_left
            simp [←card_inter_eq_k,card_le_card, inter_union_distrib_left]
          _ ≤ k + k - #(a ∩ A₁ ∪ (a ∩ A₂)) := by simp [inter_union_distrib_left]
          _ ≤ #(a ∩ A₁) + #(a ∩ A₂) - #(a ∩ A₁ ∪ (a ∩ A₂)) := by
            gcongr <;> apply inter  <;> trivial
          _ = #((a ∩ A₁) ∩ (a ∩ A₂)) := Eq.symm (card_inter (a ∩ A₁) (a ∩ A₂))
          _ = #(a ∩ (A₁ ∩ A₂)) := by congr 1;exact Eq.symm (inter_inter_distrib_left a A₁ A₂)
        have k_lt_k:= calc
          k = k + k - k := by simp
          _  < k + k - #((A₁ ∩ A₂) ∩ A₃) := by
            refine (tsub_lt_tsub_iff_left_of_le ?_).mpr inter_lt_k
            omega
          _ ≤ k + k - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) := by
            gcongr k + k - #?_
            nth_rw 2 [inter_comm]
            exact inter_subset_right
          _ ≤ #(a ∩ A₃) + #(a ∩ (A₁ ∩ A₂)) - #(a ∩ (A₃ ∩ (A₁ ∩ A₂))) := by
            solve_by_elim [Nat.sub_le_sub_right, Nat.add_le_add (inter a a_in_𝒜 A₃ A₃_in_𝒜)]
          _ = #(a ∩ A₃) + #(a ∩ (A₁ ∩ A₂))- #(a ∩ A₃ ∩ (a ∩ (A₁ ∩ A₂))) := by
            congr 2
            rw [inter_inter_distrib_left]
          _ = #(a ∩ A₃ ∪ (a ∩ (A₁ ∩ A₂)))  := by rw [card_union]
          _ = #(a ∩ (A₃ ∪ (A₁ ∩ A₂))) := by rw [inter_union_distrib_left]
          _ ≤ #(a∩U) := by
            apply card_le_card
            simp[inter_subset_inter_left,U]
            rw [union_comm,←union_assoc]
            apply_rules [inter_subset_inter_left, union_subset_union_left, inter_subset_union]
          _ ≤ k := Nat.le_of_lt_succ a_inter_le_k
        simp [GT.gt] at k_lt_k
      have card_𝒜_leq_prod : #𝒜 ≤ #(U.powerset) * #{p : Finset α| ∃ a ∈𝒜 , a\U = p} := by
        let fn : (Finset α) → (Finset α) → (Finset α) := fun a b ↦ a ∪ b
        rw [←((@card_image₂_iff _ _ _ _ fn U.powerset {p : Finset α| ∃ a ∈𝒜 , a\U = p}).mpr ?_)]
        apply card_le_card
        rw [subset_iff]
        intro x x_in_𝒜
        simp [fn]
        exists x∩U
        simp
        exists x
        rw [union_comm,sdiff_union_inter]
        simp [x_in_𝒜]
        simp [Set.InjOn,fn]
        intro a b a_in_U x x_in_𝒜 x_minus_U_eq_b a' b' a'_in_U x' x'_in_𝒜 x'_minus_U_eq_b cup_eq
        constructor
        . have a_cup_b_cap_u_eq_a : (a ∪ b) ∩ U = a := by
            rw [←x_minus_U_eq_b,inter_comm,inter_union_distrib_left]
            simpa
          have a'_cup_b'_cap_u_eq_a' : (a' ∪ b') ∩ U = a' := by
            rw [←x'_minus_U_eq_b,inter_comm,inter_union_distrib_left]
            simpa
          rw [←a_cup_b_cap_u_eq_a,←a'_cup_b'_cap_u_eq_a',cup_eq]
        . have a_cup_b_sdiff_u_eq_a : (a ∪ b) \ U = b := by
            rw [union_sdiff_distrib,←x_minus_U_eq_b,(sdiff_eq_empty_iff_subset).mpr a_in_U]
            simp
          have a'_cup_b'_sdiff_u_eq_a' : (a' ∪ b') \ U = b' := by
            rw [union_sdiff_distrib,←x'_minus_U_eq_b,(sdiff_eq_empty_iff_subset).mpr a'_in_U]
            simp
          rw [←a_cup_b_sdiff_u_eq_a,←a'_cup_b'_sdiff_u_eq_a',cup_eq]
      have card_filt_le_chooce : #(filter (fun p ↦ ∃ a ∈ 𝒜, a \ U = p) univ)
        ≤ (Fintype.card α - #(U)).choose (r - (k + 1)) * r := by
        calc
          #(filter (fun p ↦ ∃ a ∈ 𝒜, a \ U = p) univ)
            ≤ #((range (r - k)).biUnion fun n' ↦ powersetCard n' (univ \ U)) := card_le_card ?_
          _ ≤ (Fintype.card α - #U).choose (r - (k + 1)) * (r - k) := ?_
          _ ≤ (Fintype.card α - #U).choose (r - (k + 1)) * r := by apply Nat.mul_le_mul_left;omega
        . simp [subset_iff]
          intro a a_in_𝒜
          rw [←sized𝒜 a_in_𝒜,←card_sdiff_add_card_inter a U,Nat.lt_sub_iff_add_lt]
          apply Nat.add_lt_add_left
          exact succ_k_le_inter_a_U a a_in_𝒜
        . rw [mul_comm]
          nth_rw 2 [←card_range (r-k)]
          apply card_biUnion_le_card_mul
          intro lvl lvl_in_range
          simp only [mem_range, U] at lvl_in_range
          simp [Nat.choose_mono,(card_univ_diff U)]
          have lvl_lt_r_sub_succ_k :  lvl ≤ r - (k + 1) := by omega
          induction lvl_lt_r_sub_succ_k using Nat.decreasingInduction with
          | self => simp
          | of_succ lvl' _ ind =>
            have _ := @Nat.choose_le_succ_of_lt_half_left lvl' (Fintype.card α - #U) ?_
            all_goals omega
      calc
        #𝒜 ≤ #U.powerset * #(filter (fun p ↦ ∃ a ∈ 𝒜, a \ U = p) univ) := card_𝒜_leq_prod
        _ ≤ 2 ^ #U * #(filter (fun p ↦ ∃ a ∈ 𝒜, a \ U = p) univ) := by
          simp only [card_powerset, le_refl, U]
        _ ≤ 2 ^ #U * ((Fintype.card α - #U).choose (r-(k+1)) * r) := by gcongr
        _ ≤ 2 ^ #U * ((Fintype.card α - k).choose (r-(k+1)) * r) := by
          apply_rules [Nat.mul_le_mul_left,Nat.mul_le_mul_right,Nat.choose_mono,Nat.sub_le_sub_left]
        _ ≤ 2 ^ (3*r) * ((Fintype.card α - k).choose (r-(k+1)) * r) := by gcongr;simp
        _ ≤ (2 ^ (3*r) * (r * (Fintype.card α - k).choose (r-(k+1)+1) * (r-(k+1)+1)) / (Fintype.card α - k - (r - (k + 1)))) := by
          rw[Nat.le_div_iff_mul_le,mul_assoc,mul_comm ((Fintype.card α - k).choose (r - (k + 1))) r,
            mul_assoc,←Nat.choose_succ_right_eq,mul_assoc]
          omega
        _ = (2 ^ (3*r) * (r * (Fintype.card α - k).choose (r-k) * (r-k)) / (Fintype.card α - k - (r - (k + 1)))) := by congr<;>omega
        _ ≤ ( (Fintype.card α - k).choose (r-k) * (r-k) * (2 ^ (3*r) * r) / (Fintype.card α - k - (r - (k + 1)))) := by simp [←mul_assoc,Nat.le_of_eq,Nat.div_le_div_right,mul_comm]
        _ ≤ (Fintype.card α - k).choose (r - k) := ?_
      apply Nat.div_le_of_le_mul
      nth_rw 5 [mul_comm]
      nth_rw 1 [mul_assoc]
      refine Nat.mul_le_mul_left ((Fintype.card α - k).choose (r - k)) ?_
      rw [Nat.le_sub_iff_add_le,Nat.le_sub_iff_add_le,add_assoc]
      . calc
        (r - k) * (2 ^ (3 * r) * r) + (r - (k + 1) + k) ≤ (r) * (2 ^ (3 * r) * r) + r := by
          gcongr <;> omega
        _ = 2 ^ (3 * r) * r * r + r := by simp [mul_comm,mul_assoc]
        _ ≤ Fintype.card α := by omega
      all_goals omega
