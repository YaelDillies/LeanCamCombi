import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Algebra.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.GroupTheory.Submonoid.Operations
import LeanCamCombi.Mathlib.Algebra.Order.Sub.Canonical

open Finset
open scoped Classical Pointwise
open Function

variable {A B : Set ℕ} {n : ℕ}

/-- The Schnirelmann density of `A` is `1` if and only if `A` contains all the positive naturals. -/
lemma one_le_schnirelmannDensity_iff : 1 ≤ schnirelmannDensity A ↔ {0}ᶜ ⊆ A := by
  rw [schnirelmannDensity_le_one.ge_iff_eq, schnirelmannDensity_eq_one_iff]

/-- The Schnirelmann density of `A` containing `0` is `1` if and only if `A` is the naturals. -/
lemma one_le_schnirelmannDensity_iff_of_zero_mem (hA : 0 ∈ A) :
    1 ≤ schnirelmannDensity A ↔ A = Set.univ := by
  rw [schnirelmannDensity_le_one.ge_iff_eq, schnirelmannDensity_eq_one_iff_of_zero_mem hA]

noncomputable def countelements (A : Set ℕ) (n : ℕ) : ℕ := -- for teaching purposes,
  Finset.card ((Icc 1 n).filter (· ∈ A))      -- writing this is better

lemma countelements_nonneg (A : Set ℕ) (n : ℕ) : (0 ≤ countelements A n) := by positivity

lemma card_Icc_one_n_n (n : ℕ) : card (Icc 1 n) = n := by
  rw [Nat.card_Icc 1 n, add_tsub_cancel_right]

lemma countelements_le_n  (A : Set ℕ) (n : ℕ) : countelements A n ≤ n := by
  simpa [countelements] using card_filter_le (Icc 1 n) _

lemma countelements_pred (hn : n ∉ A) : countelements A (n - 1) = countelements A n := by
  repeat rw [countelements]
  refine (card_le_card $ filter_subset_filter (· ∈ A) $ Icc_subset_Icc_right ?_).antisymm ?_
  · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one]
  refine card_le_card fun x hx ↦ ?_
  rw [mem_filter]
  rw [mem_filter, mem_Icc] at hx
  refine ⟨mem_Icc.2 ⟨hx.1.1, Nat.le_pred_of_lt $ hx.1.2.lt_of_ne ?_⟩, hx.2⟩
  rintro rfl
  exact hn hx.2

lemma sumset_contains_n (hA : 0 ∈ A) (hB : 0 ∈ B) (hc : n ≤ countelements A n + countelements B n) :
    n ∈ A + B := by
  by_contra! h
  have hnA : n ∉ A := Set.not_mem_subset (Set.subset_add_left _ hB) h
  have hnB : n ∉ B := Set.not_mem_subset (Set.subset_add_right _ hA) h
  have hca : countelements A (n - 1) = countelements A n := countelements_pred hnA
  have hcb : countelements B (n - 1) = countelements B n := countelements_pred hnB
  obtain rfl | hn1 := n.eq_zero_or_pos
  · contradiction
  apply h
  have lem1 : ((Ioo 0 n).filter (· ∈ {n} - B)).card = countelements B (n - 1) := by
    rw [countelements]
    have hfim : Finset.image (n - ·) (filter (fun x ↦ x ∈ B) (Ioo 0 n)) = (filter (fun x ↦ x ∈ {n} - B) (Ioo 0 n)) := by ext; aesop
    rw [← hfim, card_image_of_injOn]
    congr
    exact (tsub_add_cancel_of_le $ Nat.succ_le_iff.2 hn1).symm
    · exact Set.InjOn.mono (fun x hx ↦ (mem_Ioo.1 (mem_filter.1 hx).1).2.le) $
        fun x hx y hy ↦ tsub_inj_right hx hy
  have lem3 : ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)).Nonempty := by
    rw [← hca, ← hcb] at hc
    have hun : Finset.card ((Ioo 0 n).filter (· ∈ A) ∪ (Ioo 0 n).filter (· ∈ {n} - B)) ≤ n - 1 := by
      rw [← filter_or, ← tsub_zero n, ← Nat.card_Ioo]
      exact card_filter_le _ _
    have hui : ((Ioo 0 n).filter (· ∈ A) ∪ (Ioo 0 n).filter (· ∈ {n} - B)).card +
        ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)).card =
          countelements A (n - 1) + countelements B (n - 1) := by
      rw [card_union_add_card_inter, ← lem1, countelements]
      congr
      exact (tsub_add_cancel_of_le $ Nat.succ_le_iff.2 hn1).symm
    have hin : 0 < Finset.card ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)) := by
      rw [← hui] at hc
      -- have hip : 0 ≤ Finset.card ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)) := by positivity
      have hun1 : Finset.card ((Ioo 0 n).filter (· ∈ A) ∪ (Ioo 0 n).filter (· ∈ {n} - B))
        + Finset.card ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)) ≤ (n - 1)
        + Finset.card ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)) := add_le_add hun le_rfl
      have hip0 : n ≤ (n - 1) + Finset.card ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)) := le_trans hc hun1
      by_contra! hip
      have hip1 : (n - 1) + Finset.card ((Ioo 0 n).filter (· ∈ A) ∩ (Ioo 0 n).filter (· ∈ {n} - B)) ≤ (n - 1) := add_le_add le_rfl hip
      have hnn : n ≤ (n - 1) := le_trans hip0 hip1
      rw [← not_lt] at hnn
      apply hnn
      rw [propext (Nat.lt_iff_le_pred hn1)]
    rwa [← Finset.card_pos]
  simp only [Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Ioo, and_imp, Set.singleton_sub, Set.mem_image, ne_eq] at lem3  -- set is nonempty iff ?
  have lem31 : (A ∩ ({n} - B) ∩ Set.Ioo 0 n).Nonempty := by
    rw [← filter_and, ← coe_nonempty, coe_filter, Set.setOf_and, Set.setOf_and, Set.setOf_mem_eq,
      Set.inter_comm] at lem3
    convert lem3 using 3 <;> ext <;> simp
  obtain ⟨_, ⟨hxA, n, rfl, x, hxB, rfl⟩, hx⟩ := lem31
  simp only [Set.mem_Ioo, Nat.succ_le_iff, tsub_pos_iff_lt, tsub_le_iff_right] at hx
  exact ⟨_, hxA, x, hxB, tsub_add_cancel_of_le hx.1.le⟩

theorem sum_schnirelmannDensity_ge_one_sumset_nat (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hAB : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) : A + B = Set.univ := by
  refine Set.eq_univ_of_forall $ fun n ↦ sumset_contains_n hA hB ?_
  obtain rfl | hn := eq_or_ne n 0
  · exact countelements_nonneg A 0
  rw [← Nat.cast_le (α := ℝ), ← one_le_div (by positivity)]
  calc
    _ ≤ _ := hAB
    _ ≤ _ := add_le_add (schnirelmannDensity_le_div hn) (schnirelmannDensity_le_div hn)
    _ = _ := by push_cast; rw [add_div]; rfl

noncomputable def next_elm (A : Set ℕ) (a : A) (n : ℕ) : ℕ :=
  if h : ((Ioc ↑a n).filter (· ∈ A)).Nonempty then ((Ioc ↑a n).filter (· ∈ A)).min' h else n

/-- **Schnirelmann's theorem** -/
theorem le_schnirelmannDensity_add (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) :
    schnirelmannDensity A + schnirelmannDensity B - schnirelmannDensity A * schnirelmannDensity B
      ≤ schnirelmannDensity (A + B) := by
  set α := schnirelmannDensity A with halpha
  set β := schnirelmannDensity B with hbeta
  have dum : α * (1 - β) + β = α + β - α * β := by ring
  rw [← dum]
  suffices main : ∀ n, (α * (1 - β) + β) * n ≤ countelements (A + B) n by
    rw [schnirelmannDensity]
    have : Nonempty {n // n ≠ 0} := by
      use 1
      trivial
    apply le_ciInf
    intro x
    have hx : (x : ℝ) ≠ 0 := by aesop
    rw [le_div_iff]
    · specialize main x
      exact main
    · positivity
  rintro n
  obtain rfl | n1 := n.eq_zero_or_pos
  · ring_nf
    positivity
  · have lem : ⋃ a : A, {c ∈ A + B | 0 < c - a ∧ c ≤ next_elm A a n} ⊆ (A + B) ∩ Icc 1 n := by
      simp only [tsub_pos_iff_lt, Set.sep_and, Set.iUnion_coe_set, Nat.lt_one_iff, coe_Icc, not_le,
        Set.subset_inter_iff, Set.iUnion_subset_iff]
      constructor
      · intro i hi x hx
        rw [Set.mem_inter_iff] at hx
        simp only [Set.mem_setOf_eq] at hx
        exact hx.1.1
      intro i hi x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
      rw [Set.mem_Icc]
      constructor
      · rcases i.eq_zero_or_pos with i0 | i1
        · rw [Nat.succ_le]
          rw [← i0]
          exact hx.1.2
        · rw [Nat.succ_le]
          apply lt_trans i1 hx.1.2
      obtain ⟨hx1, hx2, hx3⟩ := hx
      rw [next_elm] at hx3
      simp only [mem_Ioc, and_imp, ne_eq, ite_not] at hx3
      split_ifs at hx3 with h
      · norm_cast at hx3
        exact hx3.trans (mem_Ioc.1 (mem_filter.1 $ min'_mem _ _).1).2
      · simpa using hx3
    have aux : countelements (⋃ a : A, {c ∈ A + B | 0 < c - a ∧ (c : ℕ) ≤ (next_elm A a n)}) n ≤
      countelements (A + B) n := by
      rw [countelements, countelements]
      apply card_le_card
      intro y
      repeat rw [mem_filter]
      intro hy
      constructor
      · exact hy.1
      · obtain ⟨hy1, hy2⟩ := hy
        have hs : y ∈ (A + B) ∩ (Icc 1 n) := by aesop
        rw [Set.mem_inter_iff] at hs
        exact hs.1
    have claim : countelements A n + β * (n - countelements A n) ≤
      countelements (⋃ a : A, {c ∈ A + B | 0 < c - a ∧ (c : ℕ) ≤ (next_elm A a n)}) n := by
      -- simp only [tsub_pos_iff_lt, Set.sep_and, Set.iUnion_coe_set]
      --have hab (a : A) (b : B) : 0 < (b : ℕ) → (b : ℕ) ≤ (next_elm A a n) - a → (a : ℕ) + (b : ℕ) ∈ (⋃ a : A, {c ∈ A + B | 0 < c - a ∧ (c : ℕ) ≤ (next_elm A a n)}) := by sorry
      have hcc (a : A) : 1 + countelements B (next_elm A a n - a - 1) ≤ countelements {c ∈ A + B | 0 < c - a ∧ (c : ℕ) ≤ (next_elm A a n)} n := by
        sorry
      have hax (a x : A) : a ≠ x → {c ∈ A + B | 0 < c - a ∧ (c : ℕ) ≤ (next_elm A a n)} ∩ {c ∈ A + B | 0 < c - x ∧ (c : ℕ) ≤ (next_elm A x n)} = ∅ := by sorry
        -- intro hh
        -- by_contra! hin
        -- rw? at hin
      -- have hcount : ∑ a in A, (1 + countelements B (next_elm A a n - a - 1)) ≤ countelements (⋃ a : A, {c ∈ A + B | 0 < c - a ∧ (c : ℕ) ≤ (next_elm A a n)}) n := by sorry
      sorry
    have ht : countelements A n + β * (n - countelements A n) ≤ countelements (A + B) n := by
      apply le_trans claim _
      norm_cast
    have hc1 : countelements A n * (1 - β) + β * n =
      countelements A n + β * (n - countelements A n) := by ring_nf
    have hc2 : α * n * (1 - β) + β * n ≤ countelements A n * (1 - β) + β * n := by
      rw [halpha]
      by_cases hbo : β = 1
      · rw [hbo]
        simp only [sub_self, mul_zero, one_mul, zero_add, le_refl]
      · have hbn : 0 < (1 - schnirelmannDensity B) := by
          rw [hbeta] at hbo
          rw [lt_sub_iff_add_lt, zero_add, lt_iff_le_and_ne]
          exact ⟨schnirelmannDensity_le_one, hbo⟩
        simp only [add_le_add_iff_right, sub_pos, sub_neg]
        rw [← le_div_iff (hbn)]
        rw [mul_div_assoc]
        have hun : (1 - schnirelmannDensity B) / (1 - schnirelmannDensity B) = 1 := by
          rw [div_self]
          positivity
        rw [hun, mul_one]
        exact schnirelmannDensity_mul_le_card_filter
    have hc3 : α * n * (1 - β) + β * n = (α * (1 - β) + β) * n := by ring_nf
    rw [hc1] at hc2
    rw [hc3] at hc2
    exact le_trans hc2 ht

lemma schnirelmannDensity_for_two (A B : Set ℕ) : (0 ∈ A) → (0 ∈ B) →
  (1 - schnirelmannDensity (A + B)) ≤ (1 - schnirelmannDensity A) * (1 - schnirelmannDensity B) := by
  let α := schnirelmannDensity A
  have halpha : α = schnirelmannDensity A := rfl
  let β := schnirelmannDensity B
  have hbeta : β = schnirelmannDensity B := rfl
  let γ := schnirelmannDensity (A + B)
  have hgamma : γ = schnirelmannDensity (A + B) := rfl
  intro hA hB
  rw [← halpha, ← hbeta, ← hgamma]
  have h : 1 - γ ≤ 1 - (α + β - α * β) := by
    rw [sub_le_iff_le_add, add_comm_sub]
    nth_rewrite 1 [← add_zero 1]
    rw [add_le_add_iff_left, le_sub_comm, sub_zero]
    rw [sub_eq_add_neg]
    have h0 : α + β - α * β ≤ γ := by
      rw [halpha, hbeta, hgamma]
      apply le_schnirelmannDensity_add A B
      · exact hA
      · exact hB
    exact h0
  linarith



theorem mannTheorem (A B : Set ℕ) : min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ schnirelmannDensity (A + B) := by sorry
