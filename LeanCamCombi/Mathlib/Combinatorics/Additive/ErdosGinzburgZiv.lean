/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Rdrop
import Mathlib.FieldTheory.ChevalleyWarning

/-!
# The Erdős–Ginzburg–Ziv theorem

This file proves the Erdős–Ginzburg–Ziv theorem as a corollary of Chevalley-Warning. This theorem
states that among any (not necessarily distinct) `2 * n - 1` elements of `zmod n`, we can find `n`
elements of sum zero.

## Main declarations

* `zmod.exists_submultiset_eq_zero`: The Erdős–Ginzburg–Ziv theorem
-/


section

variable {α : Type _} [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α]
  [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b := by
  rw [tsub_eq_tsub_min _ b, tsub_tsub_cancel_of_le (min_le_left a _)]

end

section

variable {α : Type _} [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)]
  [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem hMul_tsub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]

theorem tsub_one_hMul (a b : α) : (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end

namespace List

variable {α : Type _} {l l' l₀ l₁ l₂ : List α} {a b : α} {m n : ℕ}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_sublist_cons_iff' : ((a::l₁) <+ b::l₂) ↔ (a::l₁) <+ l₂ ∨ a = b ∧ l₁ <+ l₂ := by
  constructor
  · rintro (_ | _)
    · exact Or.inl ‹_›
    · exact Or.inr ⟨rfl, ‹_›⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact sublist_cons_of_sublist _ h
    · rwa [cons_sublist_cons_iff]

attribute [simp] nil_subperm

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem subperm_cons_self : l <+~ a::l :=
  ⟨l, Perm.refl _, sublist_cons _ _⟩

@[simp]
theorem subperm_nil : l <+~ [] ↔ l = [] :=
  ⟨fun h => length_eq_zero.1 <| le_bot_iff.1 h.length_le, by rintro rfl; rfl⟩

theorem rtake_suffix (n : ℕ) (l : List α) : l.rtake n <:+ l :=
  drop_suffix _ _

theorem length_rtake (n : ℕ) (l : List α) : (l.rtake n).length = min n l.length :=
  (length_drop _ _).trans <| by rw [tsub_tsub_eq_min, min_comm]

@[simp]
theorem take_reverse (n : ℕ) (l : List α) : l.reverse.take n = (l.rtake n).reverse := by
  rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp]
theorem rtake_reverse (n : ℕ) (l : List α) : l.reverse.rtake n = (l.take n).reverse := by
  rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp]
theorem rtake_rtake (n m) (l : List α) : (l.rtake m).rtake n = l.rtake (min n m) := by
  rw [rtake_eq_reverse_take_reverse, ← take_reverse, take_take, rtake_eq_reverse_take_reverse]

@[simp]
theorem rdrop_append_rtake (n : ℕ) (l : List α) : l.rdrop n ++ l.rtake n = l :=
  take_append_drop _ _

theorem suffix_iff_eq_rtake : l₁ <:+ l₂ ↔ l₁ = l₂.rtake (length l₁) :=
  ⟨fun h => append_left_cancel <| (suffix_iff_eq_append.1 h).trans (rdrop_append_rtake _ _).symm,
    fun e => e.symm ▸ rtake_suffix _ _⟩

alias ⟨is_prefix.eq_take, _⟩ := prefix_iff_eq_take

alias ⟨is_suffix.eq_rtake, _⟩ := suffix_iff_eq_rtake

theorem exists_prefix_length_eq (hn : n ≤ l.length) : ∃ l', l' <+: l ∧ l'.length = n :=
  ⟨l.take n, take_prefix _ _, (length_take _ _).trans <| min_eq_left hn⟩

theorem exists_suffix_length_eq (hn : n ≤ l.length) : ∃ l', l' <:+ l ∧ l'.length = n :=
  ⟨l.rtake n, rtake_suffix _ _, (length_rtake _ _).trans <| min_eq_left hn⟩

theorem exists_sublist_length_eq (hn : n ≤ l.length) : ∃ l', l' <+ l ∧ l'.length = n :=
  ⟨l.take n, take_sublist _ _, (length_take _ _).trans <| min_eq_left hn⟩

end List

namespace Multiset

variable {α : Type _} [DecidableEq α] {s t : Multiset α} {n : ℕ}

theorem le_card_sub : s.card - t.card ≤ (s - t).card :=
  tsub_le_iff_left.2 <| (card_mono le_add_tsub).trans_eq <| card_add _ _

end Multiset

namespace Nat

theorem prime_composite_induction {P : ℕ → Prop} (zero : P 0) (one : P 1)
    (prime : ∀ p : ℕ, p.Prime → P p) (composite : ∀ a, 2 ≤ a → P a → ∀ b, 2 ≤ b → P b → P (a * b))
    (n : ℕ) : P n := by
  refine' induction_on_primes zero one _ _
  rintro p (_ | _ | a) hp ha
  · rwa [MulZeroClass.mul_zero]
  · rw [mul_one]
    exact Prime _ hp
  · exact composite _ hp.two_le (Prime _ hp) _ a.one_lt_succ_succ ha

end Nat

namespace Subtype

variable {α : Type _} {p : α → Prop} {a b : { a // p a }}

theorem coe_ne_coe : (a : α) ≠ b ↔ a ≠ b :=
  coe_inj.Not

end Subtype

namespace Multiset

variable {α : Type _} {s : Multiset α}

--TODO: Rename `multiset.coe_attach` to `multiset.attach_coe`
--TODO: Rename `multiset.coe_countp` to `multiset.countp_coe`
--TODO: Maybe change `multiset.attach` to make `multiset.coe_attach` refl?
end Multiset

namespace Nat

variable {a b : ℕ}

theorem eq_of_dvd_of_lt_two_hMul (ha : a ≠ 0) (hdvd : b ∣ a) (hlt : a < 2 * b) : a = b := by
  obtain ⟨_ | _ | c, rfl⟩ := hdvd
  · simpa using ha
  · exact mul_one _
  · cases hlt.not_le ((mul_comm _ _).trans_le <| mul_le_mul_left' (one_lt_succ_succ _) _)

end Nat

namespace ZMod

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem pow_card_sub_one (x : ZMod p) : x ^ (p - 1) = if x ≠ 0 then 1 else 0 := by
  split_ifs with hx
  · exact pow_card_sub_one_eq_one hx
  · simp [of_not_not hx, (Fact.out p.prime).one_lt]

end ZMod

open Finset MvPolynomial

open scoped BigOperators

namespace ZMod

variable {ι : Type _} {n p : ℕ} {s : Finset ι} {f : ι → ZMod p}

/-- The first multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₁ (p : ℕ) (s : Finset ι) : MvPolynomial s (ZMod p) :=
  ∑ i, X i ^ (p - 1)

/-- The second multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₂ (f : ι → ZMod p) (s : Finset ι) : MvPolynomial s (ZMod p) :=
  ∑ i : s, f i • X i ^ (p - 1)

variable {ι} [Fact p.Prime]

theorem totalDegree_f₁_add_totalDegree_f₂ :
    (f₁ p s).totalDegree + (f₂ f s).totalDegree < 2 * p - 1 := by
  refine'
    (add_le_add (total_degree_finset_sum _ _) <|
          (total_degree_finset_sum _ _).trans <| Finset.sup_mono_fun _).trans_lt
      _
  swap
  exact fun a ha => total_degree_smul_le _ _
  simp only [total_degree_X_pow, ← two_mul]
  refine' (mul_le_mul_left' Finset.sup_const_le _).trans_lt _
  rw [mul_tsub, mul_one]
  exact
    tsub_lt_tsub_left_of_le ((Fact.out p.prime).two_le.trans <| le_mul_of_one_le_left' one_le_two)
      one_lt_two

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- The prime case of the **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * p - 1`
elements of `zmod p` contain `p` elements whose sum is zero. -/
private theorem aux (hs : s.card = 2 * p - 1) (f : ι → ZMod p) :
    ∃ (t : _) (_ : t ⊆ s), t.card = p ∧ ∑ i in t, f i = 0 := by
  classical
  haveI : NeZero p := inferInstance
  -- Let `N` be the number of common roots of our polynomials `f₁` and `f₂` (`f s ff` and `f s tt`).
  set N := Fintype.card { x // eval x (f₁ p s) = 0 ∧ eval x (f₂ f s) = 0 } with hN
  -- Zero is a common root to `f₁` and `f₂`, so `N` is nonzero
  let zero_sol : { x // eval x (f₁ p s) = 0 ∧ eval x (f₂ f s) = 0 } :=
    ⟨0, by simp [f₁, f₂, map_sum, (Fact.out p.prime).one_lt]⟩
  have hN₀ : 0 < N := @Fintype.card_pos _ _ ⟨zero_sol⟩
  have hs' : 2 * p - 1 = Fintype.card s := by simp [hs]
  -- Chevalley-Warning gives us that `p ∣ n` because the total degrees of `f₁` and `f₂` are at most
  -- `p - 1`, and we have `2 * p - 1 > 2 * (p - 1)` variables.
  have hpN : p ∣ N :=
    char_dvd_card_solutions_of_add_lt p (total_degree_f₁_add_total_degree_f₂.trans_eq hs')
  -- Hence, `2 ≤ p ≤ N` and we can make a common root `x ≠ 0`.
  obtain ⟨x, hx⟩ :=
    Fintype.exists_ne_of_one_lt_card ((Fact.out p.prime).one_lt.trans_le <| Nat.le_of_dvd hN₀ hpN)
      zero_sol
  -- This common root gives us the required submultiset, namely the `a ∈ s` such that `x a ≠ 0`.
  refine' ⟨(s.attach.filter fun a => x.1 a ≠ 0).map ⟨coe, Subtype.coe_injective⟩, _, _, _⟩
  stop
    simp [subset_iff]
    exact fun x hx _ => hx
  -- From `f₁ x = 0`, we get that `p` divides the number of `a` such that `x a ≠ 0`.
  · simp only [card_map, ← Finset.filter_val, Finset.card_val, Function.comp_apply, ←
      Finset.map_val]
    refine'
      Nat.eq_of_dvd_of_lt_two_hMul (Finset.card_pos.2 _).ne' _
        ((Finset.card_filter_le _ _).trans_lt _)
    -- This number is nonzero because `x ≠ 0`.
    stop
      rw [← Subtype.coe_ne_coe, Function.ne_iff] at hx
      exact hx.imp fun a ha => mem_filter.2 ⟨Finset.mem_attach _ _, ha⟩
    stop
      rw [← CharP.cast_eq_zero_iff (ZMod p), ← Finset.sum_boole]
      simpa only [f₁, map_sum, ZMod.pow_card_sub_one, map_pow, eval_X] using x.2.1
    -- And it is at most `2 * p - 1`, so it must be `p`.
    stop
      rw [Finset.card_attach, card_to_enum_finset, hs]
      exact tsub_lt_self (mul_pos zero_lt_two (Fact.out p.prime).Pos) zero_lt_one
  -- From `f₂ x = 0`, we get that `p` divides the sum of the `a ∈ s` such that `x a ≠ 0`.
  stop simpa only [f₂, map_sum, ZMod.pow_card_sub_one, Finset.sum_map_val, Finset.sum_filter,
      smul_eval, map_pow, eval_X, mul_ite, MulZeroClass.mul_zero, mul_one] using x.2.2

--TODO: Rename `multiset.pairwise_nil` to `multiset.pairwise_zero`
/-- The **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * n - 1` elements of
`zmod n` contain `n` elements whose sum is zero. -/
theorem exists_subset_sum_eq_zero (f : ι → ZMod n) (hs : 2 * n - 1 ≤ s.card) :
    ∃ t ≤ s, t.card = n ∧ ∑ i in t, f i = 0 := by
  induction' n using Nat.prime_composite_induction with p hp
  case zero => exact ⟨∅, empty_subset _, card_empty, sum_empty⟩
  case one => obtain ⟨t, ht, hn⟩ := exists_smaller_set _ _ hs;
    exact ⟨t, ht, hn, Subsingleton.elim _ _⟩
  case prime p hp =>
    haveI := Fact.mk hp
    obtain ⟨t, hts, ht⟩ := exists_smaller_set _ _ hs
    obtain ⟨u, hut, hu⟩ := aux ht f
    exact ⟨u, hut.trans hts, hu⟩
  case composite a ha iha b hb
    ihb =>
    suffices
      ∀ n ≤ 2 * b - 1,
        ∃ m : Multiset (Multiset <| ZMod <| a * b),
          m.card = n ∧
            m.Pairwise _root_.disjoint ∧
              ∀ ⦃u : Multiset <| ZMod <| a * b⦄,
                u ∈ m → u.card = 2 * a + 1 ∧ u.Sum ∈ AddSubgroup.zmultiples (a : ZMod <| a * b) by
      obtain ⟨m, hm⟩ := this _ le_rfl
      sorry
    rintro n hn
    induction' n with n ih
    · exact ⟨0, by simp⟩
    obtain ⟨m, hm⟩ := ih (Nat.le_of_succ_le hn)
    -- have : 2 * a - 1 ≤ ((s - m.sum).map $ cast_hom (dvd_mul_right _ _) $ zmod a).card,
    -- { rw card_map,
    --   refine (le_tsub_of_add_le_left $ le_trans _ hs).trans le_card_sub,
    --   have : m.map multiset.card = repeat (2 * a - 1) n,
    --   {
    --     sorry
    --   },
    --   rw [map_multiset_sum, this, sum_repeat, ←le_tsub_iff_right, tsub_tsub_tsub_cancel_right,
    --     ←mul_tsub, ←mul_tsub_one],
    --   sorry,
    --   sorry,
    --   sorry,
    -- },
    sorry

end ZMod
