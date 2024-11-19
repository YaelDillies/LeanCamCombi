/-
Copyright (c) 2024 Yaël Dillies, Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.SuccPred
import LeanCamCombi.Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Linear lower bound on the growth of a generating set

This file proves that the growth of a set generating an infinite group is at least linear.
-/

open Subgroup
open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {X : Finset G} {n : ℕ}

@[to_additive]
lemma card_pow_lt_card_pow_succ_of_pow_ne_closure (hX : X.Nontrivial)
    (hXclosure : (X ^ n : Set G) ≠ Subgroup.closure (X : Set G)) : #(X ^ n) < #(X ^ (n + 1)) := by
  refine (hX.nonempty.card_pow_mono n.le_succ).lt_of_ne fun h ↦ hXclosure ?_
  dsimp at h
  sorry

@[to_additive]
lemma card_pow_strictMonoOn (hX : X.Nontrivial) :
    StrictMonoOn (fun n ↦ #(X ^ n)) {n | (X ^ (n - 1) : Set G) ≠ closure (X : Set G)} := by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn ↦
    card_pow_lt_card_pow_succ_of_pow_ne_closure hX hn
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
