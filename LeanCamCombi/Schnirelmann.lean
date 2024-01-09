import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Algebra.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.GroupTheory.Submonoid.Operations

open Finset
open scoped Classical Pointwise

noncomputable def countelements (A : Set ℕ) (n : ℕ) : ℕ :=  -- for teaching purposes,
  Finset.card ((Icc 1 n).filter (· ∈ A))                    -- writing this is better

lemma countelements_nonneg (A : Set ℕ) (n : ℕ) : (0 ≤ countelements A n) := by positivity
  -- -- ∧ (countelements A n ≤ n) :=
  -- -- have B := (Icc 1 n).filter (· ∈ A)
  -- rw [countelements]
  -- rw [← card_empty]
  -- -- rw [← u]
  -- apply card_le_of_subset
  -- exact empty_subset ((Icc 1 n).filter (· ∈ A))

lemma card_Icc_one_n_n (n : ℕ) : card (Icc 1 n) = n := by
  rw [Nat.card_Icc 1 n, add_tsub_cancel_right]

lemma countelements_le_n  (A : Set ℕ) (n : ℕ) : countelements A n ≤ n := by
  -- have u := filter_subset (· ∈ A) (Icc 1 n)
  rw [countelements]
  --have h := card_I
  rw [← card_Icc_one_n_n n]
  apply card_le_of_subset
  rw [card_Icc_one_n_n n]
  exact filter_subset (· ∈ A) (Icc 1 n)

lemma sumset_contains_n (A B : Set ℕ) (n : ℕ) (ha : 0 ∈ A) (hb : 0 ∈ B)
    (hc : n ≤ countelements A n + countelements B n) : n ∈ A + B := by
  by_contra! h
  have hna : n ∉ A := by
    by_contra!
    apply h
    use n
    use 0
    simp only [add_zero, and_true]
    exact { left := this, right := hb }
  have hnb : n ∉ B := by
    by_contra!
    apply h
    use 0, n
    simp only [zero_add, and_true]
    exact { left := ha, right := this}
  have hca : countelements A (n - 1) = countelements A n := by
    repeat rw [countelements]
    apply le_antisymm
    · refine card_le_of_subset ?_
      refine filter_subset_filter (· ∈ A) ?_
      refine Icc_subset_Icc_right ?_
      simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one]
    · refine card_le_of_subset ?_
      refine Iff.mpr subset_iff ?_
      intro x hx
      rw [mem_filter]
      rw [mem_filter] at hx
      constructor
      · refine Iff.mpr mem_Icc ?_
        rw [mem_Icc] at hx
        constructor
        · exact hx.1.1
        · have hhx : x < n := by
            have hxx : x ≠ n := by
             by_contra!
             apply hna
             rw [← this]
             exact hx.2
            refine Nat.lt_of_le_of_ne ?h₁ hxx
            exact hx.1.2
          exact Nat.le_pred_of_lt hhx
      · exact hx.2
  have hcb : countelements B (n - 1) = countelements B n := by
    repeat rw [countelements]
    apply le_antisymm
    · refine card_le_of_subset ?_
      refine filter_subset_filter _ ?_
      refine Icc_subset_Icc_right ?_
      simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one]
    · refine card_le_of_subset ?_
      refine Iff.mpr subset_iff ?_
      intro x hx
      rw [mem_filter]
      rw [mem_filter] at hx
      constructor
      · refine Iff.mpr mem_Icc ?_
        rw [mem_Icc] at hx
        constructor
        · exact hx.1.1
        · have hhx : x < n := by
            have hxx : x ≠ n := by
             by_contra!
             apply hnb
             rw [← this]
             exact hx.2
            refine Nat.lt_of_le_of_ne ?hh hxx
            exact hx.1.2
          exact Nat.le_pred_of_lt hhx
      · exact hx.2
  rcases n.eq_zero_or_pos with hn0 | hn1
  · rw [hn0] at hna
    rw [hn0] at hnb
    contradiction
  · have main : ∃ a b, a ∈ A ∧ b ∈ B ∧ (a : ℤ) = n - b := by
      have lem1 : Finset.card (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1))) = countelements B (n-1) := by
        rw [countelements]
        apply le_antisymm
        · simp only [Set.singleton_sub, Set.mem_image, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp]
          sorry
        · sorry
      have lem2 : (Icc 1 (n-1)).filter (· ∈ A) ∪ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1))) ⊆ Icc 1 (n-1) := by sorry
      have lem3 : (Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1))) ≠ ∅ := by sorry
      simp only [Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp, Set.singleton_sub, Set.mem_image, ne_eq] at lem3  -- set is nonempty iff ?
      have lem31 : A ∩ ({n} - B) ∩ Icc 1 (n-1) ≠ ∅ := by sorry
      rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def] at lem31
      obtain ⟨x, hx⟩ := lem31
      rw [Set.inter_def] at hx
      obtain ⟨hx1, hx2⟩ := hx
      use x, n - x
      have hnx : x < n := by
        simp only [Nat.lt_one_iff, tsub_eq_zero_iff_le, coe_Icc, not_le, Set.mem_Icc] at hx2
        zify
        zify at hx2
        rw [Int.coe_pred_of_pos hn1] at hx2
        rw [← @Int.le_sub_one_iff]
        exact hx2.2
      constructor
      · simp_all only [Set.singleton_sub, Set.mem_image, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp, Set.mem_inter_iff, coe_Icc, not_le, Set.mem_Icc]
      · constructor
        · obtain ⟨hx11, hx12⟩ := hx1
          rw [Set.mem_sub] at hx12
          obtain ⟨xx, yy, hxx, hyy, hxy⟩ := hx12
          rw [Set.mem_singleton_iff] at hxx
          rw [hxx] at hxy
          zify at hxy
          sorry
          -- zify at hxy
          -- rw [Int.cast_eq_cast_iff_Nat] at hxy
          -- rw [← hxx, ← hxy]
        sorry
    sorry

theorem sum_schnirelmannDensity_ge_one_sumset_nat (A B : Set ℕ) :
    0 ∈ A → 0 ∈ B → 1 ≤ schnirelmannDensity A + schnirelmannDensity B → Set.univ = A + B := by
  intro hA hB h
  have l := lt_trichotomy (schnirelmannDensity A) 0
  rcases l with l1 | l2 | l3
  · have ulb := schnirelmannDensity_nonneg (A := A)
    have v : schnirelmannDensity A ≠ schnirelmannDensity A := by
      refine LT.lt.ne ?h
      exact lt_of_lt_of_le l1 ulb
      -- simp only [ne_eq, not_true]
    contradiction
  · rw [l2] at h
    simp only [zero_add, ge_iff_le] at h
    have uub := schnirelmannDensity_le_one (A := B)
    have hb : schnirelmannDensity B = 1 := le_antisymm uub h
    have v := schnirelmannDensity_eq_one_iff (A := B)
    have hsub : B ⊆ A + B := by
      intro b hb
      rw [Set.mem_add]
      use 0, b
      simp only [zero_add, and_true]
      constructor
      · exact hA
      · exact hb
    rw [v] at hb
    rw [Set.Subset.antisymm_iff]
    constructor
    · have u : {0}ᶜ ⊆ A + B := le_trans hb hsub
      intro x
      rcases x.eq_zero_or_pos with rfl | hxek
      · intro hzero
        rw [Set.mem_add]
        use 0, 0
      · intro hx
        exact hsub (hb $ Nat.pos_iff_ne_zero.1 hxek)
    · exact Set.subset_univ (A + B)
  · rw [Set.Subset.antisymm_iff]
    constructor
    · have u : ∀ n : ℕ, n ≤ countelements A n + countelements B n := by
        intro n
        rcases n.eq_zero_or_pos with rfl | hnge₀
        · exact countelements_nonneg A 0
        · have ha : schnirelmannDensity A ≤ countelements A n / n := by
            rw [countelements]
            apply schnirelmannDensity_le_div
            positivity
          have hb : schnirelmannDensity B ≤ countelements B n / n := by
            rw [countelements]
            apply schnirelmannDensity_le_div
            positivity
          have hsum : schnirelmannDensity A + schnirelmannDensity B ≤ (countelements A n + countelements B n) / n := by
            rw [add_div]
            exact add_le_add ha hb
          have hf : (1 : ℝ) ≤ (countelements A n + countelements B n) / n := le_trans h hsum
          zify at hf
          zify
          rw [le_div_iff, one_mul] at hf
          · norm_cast at hf
            norm_cast
          · positivity
      intro n hn
      refine sumset_contains_n _ _ _  hA hB $ u n
    · exact Set.subset_univ (A + B)

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
  suffices main (n : ℕ) : (α * (1 - β) + β) * n ≤ countelements (A+B) n
  · rw [schnirelmannDensity]
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
  obtain rfl | n1 := n.eq_zero_or_pos
  · ring_nf
    positivity
  · have lem : ⋃ a : A, {c ∈ A + B | 0 < c - a ∧ c ≤ next_elm A a n} ⊆ (A + B) ∩ Icc 1 n
    · simp only [tsub_pos_iff_lt, Set.sep_and, Set.iUnion_coe_set, Nat.lt_one_iff, coe_Icc, not_le,
        Set.subset_inter_iff, Set.iUnion_subset_iff]
      constructor
      · intro i hi x hx
        rw [Set.mem_inter_iff] at hx
        simp only [Set.mem_setOf_eq, ge_iff_le] at hx
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
      apply card_le_of_subset
      intro y
      repeat rw [mem_filter]
      intro hy
      constructor
      · exact hy.1
      · obtain ⟨hy1, hy2⟩ := hy
        have hs : y ∈ (A + B) ∩ (Icc 1 n) := by aesop
        rw [Set.mem_inter_iff] at hs
        exact hs.1
    have claim : countelements A n + β * (n - countelements A n) ≤ countelements (⋃ a : A, {c ∈ A + B | 0 < c - a ∧ (c : ℕ) ≤ (next_elm A a n)}) n := by
      -- simp only [tsub_pos_iff_lt, Set.sep_and, Set.iUnion_coe_set]
      sorry
    have ht : countelements A n + β * (n - countelements A n) ≤ countelements (A + B) n := by
      apply le_trans claim _
      norm_cast
    have hc1 : countelements A n * (1 - β) + β * n = countelements A n + β * (n - countelements A n) := by ring_nf
    have hc2 : α * n * (1 - β) + β * n ≤ countelements A n * (1 - β) + β * n := by
      rw [halpha]
      by_cases hbo : β = 1
      · rw [hbo]
        simp only [sub_self, mul_zero, one_mul, zero_add, le_refl]
      · have hbn : 0 < (1 - schnirelmannDensity B) := by
          rw [hbeta] at hbo
          rw [lt_sub_iff_add_lt, zero_add, lt_iff_le_and_ne]
          exact ⟨schnirelmannDensity_le_one, hbo⟩
        simp only [add_le_add_iff_right, sub_pos, sub_neg, ge_iff_le]
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

lemma schnirelmannDensity_for_two (A B : Set ℕ) : (0 ∈ A) → (0 ∈ B) → (1 - schnirelmannDensity (A + B)) ≤ (1 - schnirelmannDensity A) * (1 - schnirelmannDensity B) := by
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
