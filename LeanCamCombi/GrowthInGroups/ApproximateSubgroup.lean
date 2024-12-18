import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Additive.CovBySMul
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Combinatorics.Additive.SmallTripling
import Mathlib.Combinatorics.Additive.VerySmallDoubling
import Mathlib.Tactic.Bound

-- TODO: Unsimp in mathlib
attribute [-simp] Set.image_subset_iff

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (K : ℝ) (A : Set G) : Prop where
  zero_mem : 0 ∈ A
  neg_eq_self : -A = A
  two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A

@[to_additive]
structure IsApproximateSubgroup (K : ℝ) (A : Set G) : Prop where
  one_mem : 1 ∈ A
  inv_eq_self : A⁻¹ = A
  sq_covBySMul : CovBySMul G K (A ^ 2) A

namespace IsApproximateSubgroup

@[to_additive]
lemma nonempty (hA : IsApproximateSubgroup K A) : A.Nonempty := ⟨1, hA.one_mem⟩

@[to_additive one_le]
lemma one_le (hA : IsApproximateSubgroup K A) : 1 ≤ K := by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  have hF₀ : F ≠ ∅ := by rintro rfl; simp [hA.nonempty.pow.ne_empty] at hSF
  exact hF.trans' <| by simpa [Finset.nonempty_iff_ne_empty]

@[to_additive]
lemma mono (hKL : K ≤ L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
  one_mem := hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]
lemma card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    ∀ {n}, #(A ^ n) ≤ K ^ (n - 1) * #A
  | 0 => by simpa using hA.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : ℝ) ≤ #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by omega)
      _ ≤ #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ ≤ #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (n + 1) * #A := by gcongr

@[to_additive]
lemma card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    #(A * A) ≤ K * #A := by simpa [sq] using hA.card_pow_le (n := 2)

@[to_additive]
lemma image {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup K (f '' A) where
  one_mem := ⟨1, hA.one_mem, map_one _⟩
  inv_eq_self := by simp [← Set.image_inv, hA.inv_eq_self]
  sq_covBySMul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.sq_covBySMul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : ℝ) ≤ #F := mod_cast F.card_image_le
        _ ≤ K := hF
    · simp only [← Set.image_pow, Finset.coe_image, ← Set.image_mul, smul_eq_mul] at hAF ⊢
      gcongr

@[to_additive]
lemma pi {ι : Type*} {G : ι → Type*} [Fintype ι] [∀ i, Group (G i)] {A : ∀ i, Set (G i)} {K : ι → ℝ}
    (hA : ∀ i, IsApproximateSubgroup (K i) (A i)) :
    IsApproximateSubgroup (∏ i, K i) (Set.univ.pi A) where
  one_mem i _ := (hA i).one_mem
  inv_eq_self := by simp [(hA _).inv_eq_self]
  sq_covBySMul := by
    choose F hF hFS using fun i ↦ (hA i).sq_covBySMul
    classical
    refine ⟨Fintype.piFinset F, ?_, ?_⟩
    · calc
        #(Fintype.piFinset F) = ∏ i, (#(F i) : ℝ) := by simp
        _ ≤ ∏ i, K i := by gcongr; exact hF _
    · sorry

@[to_additive]
lemma subgroup {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S} :
    IsApproximateSubgroup 1 (H : Set G) where
  one_mem := OneMemClass.one_mem H
  inv_eq_self := inv_coe_set
  sq_covBySMul := ⟨{1}, by simp⟩

open Finset in
@[to_additive]
lemma of_small_tripling [DecidableEq G] {A : Finset G} (hA₁ : 1 ∈ A) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) ≤ K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) where
  one_mem := by rw [sq, ← one_mul 1]; exact Set.mul_mem_mul hA₁ hA₁
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  sq_covBySMul := by
    replace hA := calc (#(A ^ 4 * A) : ℝ)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ ≤ K ^ 3 * #A := small_pow_of_small_tripling' (by omega) hA hAsymm
    have hA₀ : A.Nonempty := ⟨1, hA₁⟩
    obtain ⟨F, -, hF, hAF⟩ := ruzsa_covering_mul hA₀ hA
    have hF₀ : F.Nonempty := nonempty_iff_ne_empty.2 <| by rintro rfl; simp [hA₀.ne_empty] at hAF
    exact ⟨F, hF, by norm_cast; simpa [div_eq_mul_inv, pow_succ, mul_assoc, hAsymm] using hAF⟩

open Set in
@[to_additive]
lemma pow_inter_pow_covBySMul_sq_inter_sq
    (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    CovBySMul G (K ^ (m - 1) * L ^ (n - 1)) (A ^ m ∩ B ^ n) (A ^ 2 ∩ B ^ 2) := by
  classical
  obtain ⟨F₁, hF₁, hAF₁⟩ := hA.sq_covBySMul
  obtain ⟨F₂, hF₂, hBF₂⟩ := hB.sq_covBySMul
  have := hA.one_le
  choose f hf using exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul A B
  refine ⟨.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1)), ?_, ?_⟩
  · calc
      (#(.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) : ℝ)
      _ ≤ #(F₁ ^ (m - 1)) * #(F₂ ^ (n - 1)) := mod_cast Finset.card_image₂_le ..
      _ ≤ #F₁ ^ (m - 1) * #F₂ ^ (n - 1) := by gcongr <;> exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (m - 1) * L ^ (n - 1) := by gcongr
  · calc
      A ^ m ∩ B ^ n ⊆ (F₁ ^ (m - 1) * A) ∩ (F₂ ^ (n - 1) * B) := by
        gcongr <;> apply pow_subset_pow_mul_of_sq_subset_mul <;> norm_cast <;> omega
      _ = ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), a • A ∩ b • B := by
        simp_rw [← smul_eq_mul, ← iUnion_smul_set, iUnion₂_inter_iUnion₂]; norm_cast
      _ ⊆ ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), f a b • (A⁻¹ * A ∩ (B⁻¹ * B)) := by
        gcongr; exact hf ..
      _ = (Finset.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) * (A ^ 2 ∩ B ^ 2) := by
        simp_rw [hA.inv_eq_self, hB.inv_eq_self, ← sq]
        rw [Finset.coe_image₂, ← smul_eq_mul, ← iUnion_smul_set, biUnion_image2]
        simp_rw [Finset.mem_coe]

open Set in
@[to_additive]
lemma pow_inter_pow (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m)
    (hn : 2 ≤ n) :
    IsApproximateSubgroup (K ^ (2 * m - 1) * L ^ (2 * n - 1)) (A ^ m ∩ B ^ n) where
  one_mem := ⟨Set.one_mem_pow hA.one_mem, Set.one_mem_pow hB.one_mem⟩
  inv_eq_self := by simp_rw [inter_inv, ← inv_pow, hA.inv_eq_self, hB.inv_eq_self]
  sq_covBySMul := by
    refine (hA.pow_inter_pow_covBySMul_sq_inter_sq hB (by omega) (by omega)).subset ?_
      (by gcongr; exacts [hA.one_mem, hB.one_mem])
    calc
      (A ^ m ∩ B ^ n) ^ 2 ⊆ (A ^ m) ^ 2 ∩ (B ^ n) ^ 2 := Set.inter_pow_subset
      _ = A ^ (2 * m) ∩ B ^ (2 * n) := by simp [pow_mul']

end IsApproximateSubgroup

open MulAction in
/-- A finite `1`-approximate subgroup is the same thing as a finite subgroup.

Note that various sources claim this with no proof, some of them without the necessary assumptions
to make it true (eg Wikipedia before I fixed it). -/
@[to_additive (attr := simp)
"A finite `1`-approximate subgroup is the same thing as a finite subgroup.

Note that various sources claim this with no proof, some of them without the necessary assumptions
to make it true (eg Wikipedia before I fixed it)."]
lemma isApproximateSubgroup_one {S : Type*} [SetLike S G] [SubgroupClass S G] {A : Set G}
    (hA : A.Finite) :
    IsApproximateSubgroup 1 (A : Set G) ↔ ∃ H : Subgroup G, H = A where
  mp hA' := by
    classical
    lift A to Finset G using hA
    exact ⟨stabilizer G A, by simpa using
      Finset.smul_stabilizer_of_no_doubling (by simpa using hA'.card_mul_self_le) hA'.one_mem⟩
  mpr := by rintro ⟨H, rfl⟩; exact .subgroup

open Finset in
open scoped RightActions in
@[to_additive]
lemma exists_isApproximateSubgroup_of_small_doubling [DecidableEq G] {A : Finset G}
    (hA₀ : A.Nonempty) (hA : #(A ^ 2) ≤ K * #A) :
    ∃ S ⊆ (A⁻¹ * A) ^ 2, IsApproximateSubgroup (2 ^ 12 * K ^ 36) (S : Set G) ∧
      #S ≤ 16 * K ^ 12 * #A ∧ ∃ a ∈ A, #A / (2 * K) ≤ #(A ∩ S <• a) := by
  have hK : 1 ≤ K := by
    have : (#A : ℝ) ≤ #(A^2) := by simp only [pow_two A, Nat.cast_le.mpr <| card_le_card_mul_self']
    have : #A ≤ K * #A := le_trans this hA
    have : (#A > 0) → 1 ≤ K := fun hA ↦ by
      obtain ⟨x, hx₁, hx₂⟩ : ∃ (a : ℝ), a > 0 ∧ a * #A = 1 := by sorry
      sorry
    exact this <| card_pos.mpr hA₀
  -- wlog hK : 1 ≤ K with hK'
  -- . have : #(A^2) ≤ (1 : ℝ) * #A := by sorry
  --   obtain ⟨S, hS₁, hS₂⟩ := hK' hA₀ this (le_of_eq rfl)
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
