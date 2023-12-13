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

noncomputable def countelements (A : Set ℕ) (n : ℕ) : ℕ := -- for teaching purposes,
  Finset.card (Finset.filter (· ∈ A) (Finset.Icc 1 n))      -- writing this is better

lemma countelements_nonneg (A : Set ℕ) (n : ℕ) : (0 ≤ countelements A n) := by positivity
  -- -- ∧ (countelements A n ≤ n) :=
  -- -- have B := Finset.filter (· ∈ A) (Finset.Icc 1 n)
  -- rw [countelements]
  -- rw [← card_empty]
  -- -- rw [← u]
  -- apply card_le_of_subset
  -- exact empty_subset (Finset.filter (· ∈ A) (Finset.Icc 1 n))

lemma card_Icc_one_n_n (n : ℕ) : card (Finset.Icc 1 n) = n := by
  rw [Nat.card_Icc 1 n, add_tsub_cancel_right]

lemma countelements_le_n  (A : Set ℕ) (n : ℕ) : countelements A n ≤ n := by
  -- have u := filter_subset (· ∈ A) (Finset.Icc 1 n)
  rw [countelements]
  --have h := card_I
  rw [← card_Icc_one_n_n n]
  apply card_le_of_subset
  rw [card_Icc_one_n_n n]
  exact filter_subset (· ∈ A) (Finset.Icc 1 n)

-- #check countelements_nonneg
-- #check Set.inter
-- #check countelements_le_n
-- #check Real.sInf_nonneg
-- #check Set.range
-- #check schnirelmannDensity
-- #check ciInf_le
-- #check Even
-- variable (A B: Set ℕ)
-- #check A ∩ B
-- -- #check finite.sum.finite A B
-- -- #check A Set.vadd +ᵥ B
-- #check  Set.vadd
-- #check VAdd A B
-- #check A +ᵥ B
-- noncomputable def sumset (A B : Set ℕ) : Set ℕ := {a + b // a ∈ A ∧ b ∈ B}
-- #check eq_iff_le_not_lt
-- #check le_trans
-- #check zero_le_one
-- #check ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
-- #check exists_lt_of_ciInf_lt
-- #check lt_trichotomy

lemma sumset_contains_n (A B : Set ℕ) (n : ℕ) :
    0 ∈ A → 0 ∈ B → countelements A n + countelements B n > n - 1 → n ∈ A + B := by sorry

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
      use 0
      use b
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
        use 0
        use 0
      · intro hx
        exact hsub (hb $ Nat.pos_iff_ne_zero.1 hxek)
    · exact Set.subset_univ (A + B)
  · rw [Set.Subset.antisymm_iff]
    constructor
    · have u : ∀ n : ℕ, countelements A n + countelements B n ≥ n := by
        intro n
        rcases n.eq_zero_or_pos with rfl | hnge₀
        · exact countelements_nonneg A 0
        · repeat rw [schnirelmannDensity] at h
          -- rw [div_self (n : ℝ)] at h
          norm_cast at h
          sorry
      have hs := sumset_contains_n
      -- rw [u] at hs
      intro n hn
      apply hs
      · exact hA
      · exact hB
      · simp only [gt_iff_lt]
        rw [← Nat.succ_le_iff]
        simp only [ge_iff_le] at u
        rw [Nat.succ_eq_add_one, Nat.sub_add_eq_max]
        rw [Nat.max_le]
        constructor
        · exact u n
        · rcases n.eq_zero_or_pos with hnzero | hngezero
          · sorry
          · exact Nat.le_trans hngezero (u n)
    · exact Set.subset_univ (A + B)

-- #check sub_eq_add
-- #check Finset.Icc 1 0

/-- **Schnirelmann's theorem** -/
theorem le_schnirelmannDensity_add (A B : Set ℕ) :
    schnirelmannDensity A + schnirelmannDensity B - schnirelmannDensity A * schnirelmannDensity B
      ≤ schnirelmannDensity (A + B) := by sorry

-- theorem MannTheorem (A B : Set ℕ) : schnirelmannDensity (A + B) ≥  Min 1 (schnirelmannDensity A + schnirelmannDensity B) := by sorry

-- #check le_antisymm

open Real

-- hints from Bhavik

-- #check ⨅ (x : ℝ), (x + 1) -- is the Inf of (x + 1) as x ranges over ℝ
-- #check ⨅ (x : ℝ) (_ : x ≤ 1), x ^ 2 -- is the Inf of x ^ 2 as x ranges over ℝ with x ≤ 1

variable (A : Set ℕ) (n : ℕ) [DecidablePred (· ∈ A)] -- mathlib purposes, this has to be written

-- #check ((Finset.range n).filter (· ∈ A))
-- #check Finset.card
-- #check card_empty
-- #check card_le_of_subset
-- #check empty_subset
-- #check filter_subset
-- #check Nat.card_Icc


variable (A B: Set ℕ)
-- #check A + B


      -- -- rw [Mathlib.Tactic.Zify.nat_cast_eq] at hk₁
      -- push_neg at hk₁
      -- push_neg
      -- -- rw [← Nat.cast_le] at hk₁
      -- exact hk₁


      -- have t := card_Icc_one_n_n
      -- rw [division_def]
      -- rw [mul_inv_eq_iff_eq_mul₀]
      -- simp only [one_mul, Nat.cast_inj]
      -- ??
      --refine Eq.symm (Nat.pred_inj x✝ ?_ ?_)
    -- have u := schnirelmannDensity_nonneg
    -- have u' := schnirelmannDensity_le_one A
    -- by_contra h'
    -- have v : (schnirelmannDensity A < 1)  := Ne.lt_of_le h' u'
    -- rw [schnirelmannDensity] at v
    -- have hi := exists_lt_of_ciInf_lt
    -- rw? at v2

/-
      -- rw [add_le_add v v₁]
      -- have w : 1 ≤ i := by sorry  -- MAIN PROBLEM OCCURS HERE: by the definition of schnirelmannDensity, i : ℕ should be taken as i ≥ 1. Unfortunately, LEAN wants me to prove this, which is not given
      /-
      -- refine Eq.le ?mpr.h₁.a
      rw [div_self]
      · aesop  --refine Eq.symm (ciInf_pos ?mpr.h₁.a.hp)
      · norm_cast
        intro hi
        rw [hi] at v
        exact Nat.not_succ_le_zero 0 v -- <-- aesop used two times in this proof
-/-/


-- OLD VERSION OF THE PROOF WHICH WORKS EXCEPT THE PROOF OF w
      -- have v : 0 ≤ (⨅ (_ : 1 ≤ i), (i : ℝ) / i) + (- 1) := by
      --   have w : ⨅ (_ : 1 ≤ i), (i : ℝ) / i - 1 = (⨅ (_ : 1 ≤ i), (i : ℝ) / i) + (- 1) := by
      --     sorry
      --   have v₀ : 0 ≤ ⨅ (_ : 1 ≤ i), (i : ℝ) / i - 1 := by
      --     apply Real.iInf_nonneg
      --     intro hi
      --     simp only [ne_eq, Nat.cast_eq_zero, sub_nonneg]
      --     rw [div_self]
      --     simp only [ne_eq, Nat.cast_eq_zero]
      --     intro hi₀
      --     rw [hi₀] at hi
      --     exact Nat.not_succ_le_zero 0 hi
      --   rw [← w]
      --   exact v₀
      -- have v₁ : (1 : ℝ)  ≤ 1 := by rfl
      -- have v₂ : 0 + 1 ≤ (⨅ (_ : 1 ≤ i), (i : ℝ) / i) + (- 1) + 1 := add_le_add v v₁
      -- simp only [zero_add, ne_eq, Nat.cast_eq_zero, neg_add_cancel_right] at v₂
      -- exact v₂
