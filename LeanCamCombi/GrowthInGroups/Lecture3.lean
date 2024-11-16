import LeanCamCombi.GrowthInGroups.ApproximateSubgroup
import LeanCamCombi.GrowthInGroups.CardQuotient

open Fin Finset List
open scoped Pointwise

namespace GrowthInGroups.Lecture3
variable {G H : Type*} [Group G] [Group H] {A B : Set G} {K L : ℝ} {m n : ℕ}

lemma lemma_5_1 [DecidableEq G] {A : Finset G} (hA₀ : A.Nonempty) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) ≤ K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) :=
  .of_small_tripling hA₀ hAsymm hA

lemma lemma_5_2 [DecidableEq G] {A B : Finset G} (hB : B.Nonempty) (hK : #(A * B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * B / B := ruzsa_covering_mul hB hK

open scoped RightActions
lemma proposition_5_3 [DecidableEq G] {A : Finset G} (hA₀ : A.Nonempty) (hA : #(A ^ 2) ≤ K * #A) :
    ∃ S ⊆ (A⁻¹ * A) ^ 2, IsApproximateSubgroup (2 ^ 12 * K ^ 36) (S : Set G) ∧
      #S ≤ 16 * K ^ 12 * #A ∧ ∃ a ∈ A, #A / (2 * K) ≤ #(A ∩ S <• a) :=
  exists_isApproximateSubgroup_of_small_doubling hA₀ hA

lemma fact_5_5 {A : Set G} (hA : IsApproximateSubgroup K A) (π : G →* H) :
    IsApproximateSubgroup K (π '' A) := hA.image π

lemma proposition_5_6_1 (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ F : Finset G, #F ≤ K ^ (m - 1) * L ^ (n - 1) ∧ A ^ m ∩ B ^ n ⊆ F * (A ^ 2 ∩ B ^ 2) :=
  hA.exists_pow_inter_pow_subset hB hm hn

lemma proposition_5_6_2 (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hAB : (A ^ m ∩ B ^ n).Nonempty) :
    IsApproximateSubgroup (K ^ (2 * m - 1) * L ^ (2 * n - 1)) (A ^ m ∩ B ^ n) :=
  hA.pow_inter_pow hB hm hn hAB

lemma lemma_5_7 (hA : A⁻¹ = A) (hB : B⁻¹ = B) (x y : G) :
    ∃ z : G, x • A ∩ y • B ⊆ z • (A ^ 2 ∩ B ^ 2) :=
  Set.exists_smul_inter_smul_subset_smul_sq_inter_sq hA hB x y

open scoped Classical in
lemma lemma_5_8_1 {H : Subgroup G} [H.Normal] {A : Finset G} :
    #((A ^ m).image <| QuotientGroup.mk' H) * #{x ∈ A ^ n | x ∈ H} ≤ #(A ^ (m + n)) :=
  card_pow_quotient_mul_pow_inter_subgroup

open scoped Classical in
lemma lemma_5_8_2 {H : Subgroup G} [H.Normal] {A : Finset G} (hAsymm : A⁻¹ = A) :
    #A ≤ #(A.image <| QuotientGroup.mk' H) * #{x ∈ A ^ 2 | x ∈ H} :=
  le_card_quotient_mul_sq_inter_subgroup hAsymm

end GrowthInGroups.Lecture3
