import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Additive.SmallTripling
import Mathlib.Tactic.Bound
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Set.Basic
import LeanCamCombi.Mathlib.Algebra.Group.Subgroup.Pointwise
import LeanCamCombi.Mathlib.Combinatorics.Additive.RuzsaCovering
import LeanCamCombi.Mathlib.Data.Finset.Basic
import LeanCamCombi.Mathlib.Data.Set.Basic
import LeanCamCombi.Mathlib.Data.Set.Lattice
import LeanCamCombi.Mathlib.Data.Set.Pointwise.SMul

-- TODO: Unsimp in mathlib
attribute [-simp] Set.image_subset_iff

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (K : ℝ) (A : Set G) : Prop where
  nonempty : A.Nonempty
  neg_eq_self : -A = A
  exists_two_nsmul_subset_add : ∃ F : Finset G, #F ≤ K ∧ 2 • A ⊆ F + A

@[to_additive]
structure IsApproximateSubgroup (K : ℝ) (A : Set G) : Prop where
  nonempty : A.Nonempty
  inv_eq_self : A⁻¹ = A
  exists_sq_subset_mul : ∃ F : Finset G, #F ≤ K ∧ A ^ 2 ⊆ F * A

namespace IsApproximateSubgroup

@[to_additive one_le]
lemma one_le (hA : IsApproximateSubgroup K A) : 1 ≤ K := by
  obtain ⟨F, hF, hSF⟩ := hA.exists_sq_subset_mul
  have hF₀ : F ≠ ∅ := by rintro rfl; simp [hA.nonempty.pow.ne_empty] at hSF
  exact hF.trans' <| by simpa [Finset.nonempty_iff_ne_empty]

@[to_additive]
lemma mono (hKL : K ≤ L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
  nonempty := hA.nonempty
  inv_eq_self := hA.inv_eq_self
  exists_sq_subset_mul := let ⟨F, hF, hSF⟩ := hA.exists_sq_subset_mul; ⟨F, hF.trans hKL, hSF⟩

@[to_additive]
lemma card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    ∀ {n}, #(A ^ n) ≤ K ^ (n - 1) * #A
  | 0 => by simpa using hA.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hA.exists_sq_subset_mul
    calc
      (#(A ^ (n + 2)) : ℝ) ≤ #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by omega)
      _ ≤ #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ ≤ #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (n + 1) * #A := by gcongr

@[to_additive]
lemma image {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup K (f '' A) where
  nonempty := hA.nonempty.image _
  inv_eq_self := by simp [← Set.image_inv', hA.inv_eq_self]
  exists_sq_subset_mul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.exists_sq_subset_mul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : ℝ) ≤ #F := mod_cast F.card_image_le
        _ ≤ K := hF
    · simp only [← Set.image_pow, Finset.coe_image, ← Set.image_mul]
      gcongr

@[to_additive]
lemma pi {ι : Type*} {G : ι → Type*} [Fintype ι] [∀ i, Group (G i)] {A : ∀ i, Set (G i)} {K : ι → ℝ}
    (hA : ∀ i, IsApproximateSubgroup (K i) (A i)) :
    IsApproximateSubgroup (∏ i, K i) (Set.univ.pi A) where
  nonempty := Set.univ_pi_nonempty_iff.2 fun i ↦ (hA i).nonempty
  inv_eq_self := by simp [(hA _).inv_eq_self]
  exists_sq_subset_mul := by
    choose F hF hFS using fun i ↦ (hA i).exists_sq_subset_mul
    classical
    refine ⟨Fintype.piFinset F, ?_, ?_⟩
    · calc
        #(Fintype.piFinset F) = ∏ i, (#(F i) : ℝ) := by simp
        _ ≤ ∏ i, K i := by gcongr; exact hF _
    · sorry

@[to_additive]
lemma subgroup {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S} :
    IsApproximateSubgroup 1 (H : Set G) where
  nonempty := .of_subtype
  inv_eq_self := inv_coe_set
  exists_sq_subset_mul := ⟨{1}, by simp⟩

open Finset in
@[to_additive]
lemma of_small_tripling [DecidableEq G] {A : Finset G} (hA₀ : A.Nonempty) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) ≤ K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) where
  nonempty := hA₀.to_set.pow
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  exists_sq_subset_mul := by
    replace hA := calc (#(A ^ 4 * A) : ℝ)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ ≤ K ^ 3 * #A := small_pow_of_small_tripling' (by omega) hA hAsymm
    obtain ⟨F, -, hF, hAF⟩ := ruzsa_covering_mul hA₀ hA
    have hF₀ : F.Nonempty := nonempty_iff_ne_empty.2 <| by rintro rfl; simp [hA₀.ne_empty] at hAF
    exact ⟨F, hF, by norm_cast; simpa [div_eq_mul_inv, pow_succ, mul_assoc, hAsymm] using hAF⟩

open Set in
@[to_additive]
lemma exists_pow_inter_pow_subset (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ F : Finset G, #F ≤ K ^ (m - 1) * L ^ (n - 1) ∧ A ^ m ∩ B ^ n ⊆ F * (A ^ 2 ∩ B ^ 2) := by
  classical
  obtain ⟨F₁, hF₁, hAF₁⟩ := hA.exists_sq_subset_mul
  obtain ⟨F₂, hF₂, hBF₂⟩ := hB.exists_sq_subset_mul
  have := hA.one_le
  choose f hf using exists_smul_inter_smul_subset_smul_sq_inter_sq hA.inv_eq_self hB.inv_eq_self
  refine ⟨.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1)), ?_, ?_⟩
  · calc
      (#(.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) : ℝ)
      _ ≤ #(F₁ ^ (m - 1)) * #(F₂ ^ (n - 1)) := mod_cast Finset.card_image₂_le ..
      _ ≤ #F₁ ^ (m - 1) * #F₂ ^ (n - 1) := by gcongr <;> exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (m - 1) * L ^ (n - 1) := by gcongr
  · calc
      A ^ m ∩ B ^ n ⊆ (F₁ ^ (m - 1) * A) ∩ (F₂ ^ (n - 1) * B) := by
        gcongr <;> apply pow_subset_pow_mul_of_sq_subset_mul <;> assumption
      _ = ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), a • A ∩ b • B := by
        simp_rw [← smul_eq_mul, ← iUnion_smul_set, iUnion₂_inter_iUnion₂]; norm_cast
      _ ⊆ ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), f a b • (A ^ 2 ∩ B ^ 2) := by gcongr; exact hf ..
      _ = (Finset.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) * (A ^ 2 ∩ B ^ 2) := by
        rw [Finset.coe_image₂, ← smul_eq_mul, ← iUnion_smul_set, biUnion_image2]
        simp_rw [Finset.mem_coe]

open Set in
@[to_additive]
lemma pow_inter_pow (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hAB : (A ^ m ∩ B ^ n).Nonempty) :
    IsApproximateSubgroup (K ^ (2 * m - 1) * L ^ (2 * n - 1)) (A ^ m ∩ B ^ n) where
  nonempty := hAB
  inv_eq_self := by simp_rw [inter_inv, ← inv_pow, hA.inv_eq_self, hB.inv_eq_self]
  exists_sq_subset_mul := by
    obtain ⟨F, hF, hABF⟩ := hA.exists_pow_inter_pow_subset hB hm hn
    sorry

end IsApproximateSubgroup

@[to_additive (attr := simp)]
lemma isApproximateSubgroup_one {S : Type*} [SetLike S G] [SubgroupClass S G] {A : Set G} :
    IsApproximateSubgroup 1 (A : Set G) ↔ ∃ H : Subgroup G, A = H := by
  refine ⟨fun hA ↦ ?_, by rintro ⟨H, rfl⟩; exact .subgroup⟩
  sorry

open Finset in
open scoped RightActions in
@[to_additive]
lemma exists_isApproximateSubgroup_of_small_doubling [DecidableEq G] {A : Finset G}
    (hA₀ : A.Nonempty) (hA : #(A ^ 2) ≤ K * #A) :
    ∃ S ⊆ (A⁻¹ * A) ^ 2, IsApproximateSubgroup (2 ^ 12 * K ^ 36) (S : Set G) ∧
      #S ≤ 16 * K ^ 12 * #A ∧ ∃ a ∈ A, #A / (2 * K) ≤ #(A ∩ S <• a) := by
  have hK : 1 ≤ K := sorry
  let S : Finset G := {g ∈ A⁻¹ * A | #A / (2 * K) ≤ #(A <• g ∩ A)}
  have hS₀ : S.Nonempty := ⟨1, by simp [S, hA₀.ne_empty]; bound⟩
  have hSA : S ⊆ A⁻¹ * A := filter_subset ..
  have hSsymm : S⁻¹ = S := by ext; simp [S]; simp [← mem_inv']; sorry
  have hScard :=
    calc
      (#S : ℝ) ≤ #(A⁻¹ * A) := by gcongr
      _ ≤ K ^ 2 * #A := sorry
  refine ⟨S ^ 2, by gcongr, ⟨sorry, sorry, sorry⟩, ?_, ?_⟩
  sorry
  sorry
