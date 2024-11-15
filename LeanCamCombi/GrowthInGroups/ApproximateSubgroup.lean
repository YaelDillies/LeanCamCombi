import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Additive.SmallTripling
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Set.Basic
import LeanCamCombi.Mathlib.Combinatorics.Additive.RuzsaCovering
import LeanCamCombi.Mathlib.Data.Finset.Basic

open scoped Finset Pointwise

variable {G : Type*} [Group G] {S : Set G} {K L : ℝ} {n : ℕ}

structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (S : Set G) (K : ℝ) : Prop where
  nonempty : S.Nonempty
  neg_eq_self : -S = S
  exists_two_nsmul_subset_add : ∃ F : Finset G, #F ≤ K ∧ 2 • S ⊆ F + S

@[to_additive]
structure IsApproximateSubgroup (S : Set G) (K : ℝ) : Prop where
  nonempty : S.Nonempty
  inv_eq_self : S⁻¹ = S
  exists_sq_subset_mul : ∃ F : Finset G, #F ≤ K ∧ S ^ 2 ⊆ F * S

namespace IsApproximateSubgroup

@[to_additive one_le]
lemma one_le (hS : IsApproximateSubgroup S K) : 1 ≤ K := by
  obtain ⟨F, hF, hSF⟩ := hS.exists_sq_subset_mul
  have hF₀ : F ≠ ∅ := by rintro rfl; simp [hS.nonempty.pow.ne_empty] at hSF
  exact hF.trans' <| by simpa [Finset.nonempty_iff_ne_empty]

@[to_additive]
lemma mono (hKL : K ≤ L) (hS : IsApproximateSubgroup S K) : IsApproximateSubgroup S L where
  nonempty := hS.nonempty
  inv_eq_self := hS.inv_eq_self
  exists_sq_subset_mul := let ⟨F, hF, hSF⟩ := hS.exists_sq_subset_mul; ⟨F, hF.trans hKL, hSF⟩

@[to_additive]
lemma card_pow_le [DecidableEq G] {S : Finset G} (hS : IsApproximateSubgroup (S : Set G) K) :
    ∀ {n}, #(S ^ n) ≤ K ^ (n - 1) * #S
  | 0 => by simpa using hS.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hS.exists_sq_subset_mul
    calc
      (#(S ^ (n + 2)) : ℝ) ≤ #(F ^ (n + 1) * S) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by omega)
      _ ≤ #(F ^ (n + 1)) * #S := mod_cast Finset.card_mul_le
      _ ≤ #F ^ (n + 1) * #S := by gcongr; exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (n + 1) * #S := by gcongr

@[to_additive]
lemma pi {ι : Type*} {G : ι → Type*} [Fintype ι] [∀ i, Group (G i)] {S : ∀ i, Set (G i)} {K : ι → ℝ}
    (hS : ∀ i, IsApproximateSubgroup (S i) (K i)) :
    IsApproximateSubgroup (Set.univ.pi S) (∏ i, K i) where
  nonempty := Set.univ_pi_nonempty_iff.2 fun i ↦ (hS i).nonempty
  inv_eq_self := by simp [(hS _).inv_eq_self]
  exists_sq_subset_mul := by
    choose F hF hFS using fun i ↦ (hS i).exists_sq_subset_mul
    classical
    refine ⟨Fintype.piFinset F, ?_, ?_⟩
    · calc
        #(Fintype.piFinset F) = ∏ i, (#(F i) : ℝ) := by simp
        _ ≤ ∏ i, K i := by gcongr; exact hF _
    · sorry

open Finset in
@[to_additive]
lemma of_small_tripling [DecidableEq G] {A : Finset G} (hA₀ : A.Nonempty) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) ≤ K * #A) : IsApproximateSubgroup (A ^ 2 : Set G) (K ^ 3) where
  nonempty := hA₀.to_set.pow
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  exists_sq_subset_mul := by
    replace hA := calc (#(A ^ 4 * A) : ℝ)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ ≤ K ^ 3 * #A := small_pow_of_small_tripling' (by omega) hA hAsymm
    obtain ⟨F, -, hF, hAF⟩ := ruzsa_covering_mul hA₀ hA
    have hF₀ : F.Nonempty := nonempty_iff_ne_empty.2 <| by rintro rfl; simp [hA₀.ne_empty] at hAF
    exact ⟨F, hF, by norm_cast; simpa [div_eq_mul_inv, pow_succ, mul_assoc, hAsymm] using hAF⟩

end IsApproximateSubgroup
