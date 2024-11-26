/-
Copyright (c) 2024 Yaël Dillies, Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.SuccPred
import LeanCamCombi.Mathlib.Algebra.Group.Subgroup.Pointwise

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Linear lower bound on the growth of a generating set

This file proves that the growth of a set generating an infinite group is at least linear.
-/

open Subgroup
open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {X : Finset G} {n : ℕ}

@[to_additive]
lemma card_pow_lt_card_pow_succ_of_pow_ne_closure (hX : (1 : G) ∈ X) (hX' : X.Nontrivial)
    (hXclosure : (X ^ n : Set G) ≠ Subgroup.closure (X : Set G)) : #(X ^ n) < #(X ^ (n + 1)) := by
  -- wlog n >= 1
  have : n = 0 ∨ n ≥ 1 := by
    obtain rfl | ⟨n, hn⟩ := n
    all_goals simp
  obtain rfl | hn := this
  . simp only [pow_zero, card_one, zero_add, pow_one, gt_iff_lt, Finset.one_lt_card_iff_nontrivial.mpr hX']

  have hsub : ∀ n, X^n ⊆ X^(n + 1) := fun n ↦ by
    calc X^n = {1} * X^n := by exact Eq.symm (one_mul (X ^ n))
           _ ⊆ X * X^n := by
            have : {1} ⊆ X := singleton_subset_iff.mpr hX
            exact mul_subset_mul this fun ⦃a⦄ a ↦ a
           _ = X^(n + 1) := Eq.symm (pow_succ' X n)
  have hsub : ∀ (n m), n ≤ m → X^n ⊆ X^m := fun n m hnm ↦ pow_subset_pow_of_one_mem hX hnm
  by_contra hcontra
  simp at hcontra
  -- have hcard : ∀ n ≥ 1, #(X^n) = #(X^(n + 1)) := by sorry
  have heq : X^n = X^(n + 1) :=
    eq_of_subset_of_card_le (hsub n (n + 1) <| Nat.le_add_right n 1) hcontra
  have heq' : ∀ d ≥ 0, X^(n + d) = X^n := fun d hd ↦ by
    induction' d with d hd'
    . rw [add_zero]
    . specialize hd' (Nat.zero_le d)
      rw [pow_add, pow_one] at heq
      rw [← add_assoc n d 1, pow_add, pow_one, hd', ← heq]
  have heq'' : ∀ d ≥ 0, (X : Set G)^(n + d) = X^n := fun d hd ↦ by
    specialize heq' d hd
    norm_cast

  have hXclosure' : Subgroup.closure (X : Set G) = Subgroup.closure (X^n : Set G) := by
    ext x
    unfold closure
    refine ⟨fun hx H hH ↦ ?_, fun hx H hH ↦ ?_⟩
    . obtain ⟨H, hH, _⟩ := hH
      specialize hsub 1 n hn
      rw [pow_one] at hsub
      simp at hx ⊢
      intro hH
      refine hx H (fun a ha ↦ ?_)
      norm_cast at hH hsub ⊢
      exact hH <| hsub <| (by norm_cast)
    . obtain ⟨H, hH, _⟩ := hH
      simp at hx ⊢
      intro hH
      refine hx H ?_
      intros a ha
      have : ∀ (N : ℕ), (X : Set G)^N ⊆ H := fun N ↦ by
        induction' N with N hN
        . simp only [pow_zero, Set.one_subset, hH hX]
        . rw [pow_add, pow_one]
          rintro _ ⟨b, hb, c, hc, rfl⟩
          exact mul_mem (hN hb) (hH hc)
      exact this n ha

  rw [hXclosure'] at hXclosure
  have hX1 : 1 ∈ X^n := one_mem_pow hX

  refine hXclosure ?_
  unfold closure
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  . rintro _ ⟨H, rfl⟩ K ⟨hK, rfl⟩
    exact hK hx
  . let Xgp : Subgroup G := {
      carrier := X^n
      mul_mem' := by
        intros a b ha hb
        rw [← heq'' n (Nat.zero_le n)]
        norm_cast at ha hb ⊢
        rw [pow_add, mem_mul]
        exact ⟨a, ha, b, hb, rfl⟩
      one_mem' := by norm_cast
      inv_mem' := by
        intros y hy
        simp at hy ⊢
        have : y • X^n ⊆ X^n := by
          nth_rw 2 [← heq' n (Nat.zero_le n)]
          rw [pow_add]
          exact smul_finset_subset_mul (by norm_cast at hy)
        have : y • X^n = X^n := eq_of_subset_of_card_le this (le_of_eq (card_smul_finset y <| X^n).symm)
        rw [← this, mem_smul_finset] at hX1
        obtain ⟨z, hz, hz'⟩ := hX1
        obtain rfl := DivisionMonoid.inv_eq_of_mul y z hz'
        norm_cast
    }
    specialize hx Xgp
    simp only [Set.mem_setOf_eq, Set.mem_range, SetLike.mem_coe, forall_exists_index] at hx
    specialize hx Xgp ?_
    . ext y
      refine ⟨fun hy ↦ ?_, fun hy ↦ by simp only [Set.mem_iInter, hy, implies_true]⟩
      apply hy
      unfold Xgp
      simp only [id_eq, eq_mp_eq_cast, eq_mpr_eq_cast, smul_eq_mul, coe_set_mk, subset_refl,
        nonempty_prop, Set.range_const, Set.mem_singleton_iff]
    . rw [← mem_carrier] at hx
      simpa only

@[to_additive]
lemma card_pow_strictMonoOn (hX : X.Nontrivial) :
    StrictMonoOn (fun n ↦ #(X ^ n)) {n | (X ^ (n - 1) : Set G) ≠ closure (X : Set G)} := by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn ↦
    card_pow_lt_card_pow_succ_of_pow_ne_closure sorry hX hn
  rintro - - n hn m ⟨-, hmn⟩ hm
  apply hn
  obtain rfl | hm₀ := m.eq_zero_or_pos
  · simp at hm
    rw [← hm]
    rw [eq_comm, coe_set_eq_one, closure_eq_bot_iff] at hm
    cases hX.not_subset_singleton hm
  calc (X : Set G) ^ (n - 1) = X ^ (n - m) * X ^ (m - 1) := by rw [← pow_add]; congr 1; omega
  _ = closure (X : Set G) := by rw [hm, Set.mul_subgroupClosure_pow hX.nonempty.to_set]

@[to_additive]
lemma card_pow_strictMono (hXclosure : (closure (X : Set G) : Set G).Infinite)
    (hX : X.Nontrivial) : StrictMono fun n ↦ #(X ^ n) := by
  have h n : (X ^ (n - 1) : Set G) ≠ closure (X : Set G) :=
    fun h ↦ by simp [← h, ← coe_pow] at hXclosure
  simpa [h] using card_pow_strictMonoOn hX

/-- The growth of a set generating an infinite group is at least linear. -/
@[to_additive "The growth of a set generating an infinite group is at least linear."]
lemma add_one_le_card_pow (hXclosure : (closure (X : Set G) : Set G).Infinite) (hX : X.Nontrivial) :
    ∀ n, n + 1 ≤ #(X ^ n)
  | 0 => by simp
  | n + 1 => (add_one_le_card_pow hXclosure hX _).trans_lt <|
    card_pow_strictMono (by simp [hXclosure, Set.infinite_univ]) hX n.lt_succ_self

end Finset
