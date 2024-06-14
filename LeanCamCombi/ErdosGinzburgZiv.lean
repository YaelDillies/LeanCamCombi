/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Multiset.Fintype
import Mathlib.FieldTheory.ChevalleyWarning
import LeanCamCombi.Mathlib.Algebra.Order.Ring.Canonical
import LeanCamCombi.Mathlib.Data.Multiset.Basic
import LeanCamCombi.Mathlib.Data.Nat.Defs
import LeanCamCombi.Mathlib.FieldTheory.Finite.Basic
import LeanCamCombi.Mathlib.RingTheory.Int.Basic

/-!
# The Erdős–Ginzburg–Ziv theorem

This file proves the Erdős–Ginzburg–Ziv theorem as a corollary of Chevalley-Warning. This theorem
states that among any (not necessarily distinct) `2 * n - 1` elements of `ZMod n`, we can find `n`
elements of sum zero.

## Main declarations

* `ZMod.exists_submultiset_eq_zero`: The Erdős–Ginzburg–Ziv theorem
-/

namespace Finset
variable {α β : Type*} [AddCommMonoidWithOne β]

@[simp] lemma card_filter_attach (p : α → Prop) [DecidablePred p] (s : Finset α) :
   (filter (fun a : s ↦ p ↑a) s.attach).card = (filter p s).card := sorry

end Finset

open Multiset MvPolynomial
open scoped BigOperators

namespace ZMod
variable {n p : ℕ} [Fact p.Prime] {s : Multiset (ZMod p)}

/-- The first multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₁ (s : Multiset (ZMod p)) : MvPolynomial s.toEnumFinset (ZMod p) :=
  ∑ x in s.toEnumFinset.attach, X x ^ (p - 1)

/-- The second multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₂ (s : Multiset (ZMod p)) : MvPolynomial s.toEnumFinset (ZMod p) :=
  ∑ x in s.toEnumFinset.attach, x.1.1 • X x ^ (p - 1)

private lemma totalDegree_f₁_add_totalDegree_f₂ :
    (f₁ s).totalDegree + (f₂ s).totalDegree < 2 * p - 1 := by
  refine (add_le_add (totalDegree_finset_sum _ _) $ (totalDegree_finset_sum _ _).trans $
    Finset.sup_mono_fun fun a _ ↦ totalDegree_smul_le _ _).trans_lt ?_
  simp only [totalDegree_X_pow, ← two_mul]
  refine (mul_le_mul_left' Finset.sup_const_le _).trans_lt ?_
  rw [mul_tsub, mul_one]
  exact tsub_lt_tsub_left_of_le ((Fact.out : p.Prime).two_le.trans $
    le_mul_of_one_le_left' one_le_two) one_lt_two

/-- The prime case of the **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * p - 1`
elements of `ZMod p` contain `p` elements whose sum is zero. -/
private lemma aux (hs : Multiset.card s = 2 * p - 1) :
    ∃ t ≤ s, Multiset.card t = p ∧ t.sum = 0 := by
  haveI : NeZero p := inferInstance
  -- Let `N` be the number of common roots of our polynomials `f₁` and `f₂` (`f s ff` and `f s tt`).
  set N := Fintype.card {x // eval x (f₁ s) = 0 ∧ eval x (f₂ s) = 0}
  -- Zero is a common root to `f₁` and `f₂`, so `N` is nonzero
  let zero_sol : {x // eval x (f₁ s) = 0 ∧ eval x (f₂ s) = 0} :=
    ⟨0, by simp [f₁, f₂, map_sum, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]⟩
  have hN₀ : 0 < N := @Fintype.card_pos _ _ ⟨zero_sol⟩
  have hs' : 2 * p - 1 = Fintype.card s.toEnumFinset := by simp [hs]
  -- Chevalley-Warning gives us that `p ∣ n` because the total degrees of `f₁` and `f₂` are at most
  -- `p - 1`, and we have `2 * p - 1 > 2 * (p - 1)` variables.
  have hpN : p ∣ N := char_dvd_card_solutions_of_add_lt p
    (totalDegree_f₁_add_totalDegree_f₂.trans_eq hs')
  -- Hence, `2 ≤ p ≤ N` and we can make a common root `x ≠ 0`.
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card ((Fact.out : p.Prime).one_lt.trans_le $
    Nat.le_of_dvd hN₀ hpN) zero_sol
  -- This common root gives us the required submultiset, namely the `a ∈ s` such that `x a ≠ 0`.
  -- Note that we need `Multiset.toEnumFinset` to distinguish duplicated elements of `s`.
  refine ⟨(s.toEnumFinset.attach.filter $ fun a ↦ x.1 a ≠ 0).1.map
    (Prod.fst ∘ ((↑) : s.toEnumFinset → ZMod p × ℕ)), le_iff_count.2 $ fun a ↦ ?_, ?_, ?_⟩
  · simp only [← Finset.filter_val, Finset.card_val, Function.comp_apply, count_map]
    refine (Finset.card_le_card $ Finset.filter_subset_filter _ $
      Finset.filter_subset _ _).trans_eq ?_
    refine (Finset.card_filter_attach (fun c : ZMod p × ℕ ↦ a = c.1) _).trans ?_
    simp [toEnumFinset_filter_eq]
  -- From `f₁ x = 0`, we get that `p` divides the number of `a` such that `x a ≠ 0`.
  · simp only [card_map, ← Finset.filter_val, Finset.card_val, Function.comp_apply,
      count_map, ← Finset.map_val]
    refine Nat.eq_of_dvd_of_lt_two_mul (Finset.card_pos.2 ?_).ne' ?_ $
      (Finset.card_filter_le _ _).trans_lt ?_
    -- This number is nonzero because `x ≠ 0`.
    · rw [← Subtype.coe_ne_coe, Function.ne_iff] at hx
      exact hx.imp (fun a ha ↦ mem_filter.2 ⟨Finset.mem_attach _ _, ha⟩)
    · rw [← CharP.cast_eq_zero_iff (ZMod p), ← Finset.sum_boole]
      simpa only [f₁, map_sum, ZMod.pow_card_sub_one, map_pow, eval_X] using x.2.1
    -- And it is at most `2 * p - 1`, so it must be `p`.
    · rw [Finset.card_attach, card_toEnumFinset, hs]
      exact tsub_lt_self (mul_pos zero_lt_two (Fact.out : p.Prime).pos) zero_lt_one
  -- From `f₂ x = 0`, we get that `p` divides the sum of the `a ∈ s` such that `x a ≠ 0`.
  · simpa only [f₂, map_sum, ZMod.pow_card_sub_one, Finset.sum_map_val, Finset.sum_filter,
      smul_eval, map_pow, eval_X, mul_ite, mul_zero, mul_one] using x.2.2

--TODO: Rename `Multiset.pairwise_nil` to `Multiset.pairwise_zero`

/-- The **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * n - 1` elements of
`ZMod n` contain `n` elements whose sum is zero. -/
lemma exists_submultiset_eq_zero {s : Multiset (ZMod n)} (hs : 2 * n - 1 ≤ Multiset.card s) :
    ∃ t ≤ s, Multiset.card t = n ∧ t.sum = 0 := by
  induction n using Nat.prime_composite_induction
  case zero => exact ⟨0, s.zero_le, card_zero, sum_zero⟩
  case one => obtain ⟨t, ht, hn⟩ := exists_le_card_eq hs; exact ⟨t, ht, hn, Subsingleton.elim _ _⟩
  case prime p hp =>
    haveI := Fact.mk hp
    obtain ⟨t, hts, ht⟩ := exists_le_card_eq hs
    obtain ⟨u, hut, hu⟩ := aux ht
    exact ⟨u, hut.trans hts, hu⟩
  case composite a ha iha b hb ihb =>
    suffices ∀ n ≤ 2 * b - 1, ∃ m : Multiset (Multiset $ ZMod $ a * b), Multiset.card m = n ∧
      m.Pairwise _root_.Disjoint ∧ ∀ ⦃u : Multiset $ ZMod $ a * b⦄, u ∈ m →
        Multiset.card u = 2 * a + 1 ∧ u.sum ∈ AddSubgroup.zmultiples (a : ZMod $ a * b) by
      obtain ⟨m, hm⟩ := this _ le_rfl
      sorry
    rintro n hn
    induction' n with n ih
    · exact ⟨0, by simp⟩
    obtain ⟨m, hm⟩ := ih (Nat.le_of_succ_le hn)
    have : 2 * a - 1 ≤ Multiset.card ((s - m.sum).map $ castHom (dvd_mul_right _ _) $ ZMod a) := by
      rw [card_map]
      refine (le_tsub_of_add_le_left $ le_trans ?_ hs).trans le_card_sub
      have : m.map Multiset.card = replicate (2 * a - 1) n := sorry
      rw [map_multiset_sum, this, sum_replicate, ← le_tsub_iff_right, tsub_tsub_tsub_cancel_right,
        ← mul_tsub, ← mul_tsub_one]
      sorry
      sorry
      sorry
    sorry

end ZMod
