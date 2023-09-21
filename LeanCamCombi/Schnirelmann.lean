import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Nat.Interval
import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Prime
-- import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.Data.Set.Pointwise.SMul
-- import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Init.Algebra.Order
-- import Mathlib.Algebra.Ring.BooleanRing

open Finset Classical

noncomputable def countelements (A : Set ℕ) (n : ℕ) : ℕ := -- for teaching purposes,
  Finset.card (Finset.filter (· ∈ A) (Finset.Icc 1 n))      -- writing this is better


lemma countelements_nonneg (A : Set ℕ) (n : ℕ): (0 ≤ countelements A n) := by positivity
  -- -- ∧ (countelements A n ≤ n) :=
  -- -- have B := Finset.filter (· ∈ A) (Finset.Icc 1 n)
  -- rw [countelements]
  -- rw [← card_empty]
  -- -- rw [← u]
  -- apply card_le_of_subset
  -- exact empty_subset (Finset.filter (· ∈ A) (Finset.Icc 1 n))

lemma card_Icc_one_n_n (n : ℕ) : card (Finset.Icc 1 n) = n := by
  rw [Nat.card_Icc 1 n]
  simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]


lemma countelements_le_n  (A : Set ℕ) (n : ℕ) : (countelements A n ≤ n) := by
  -- have u := filter_subset (· ∈ A) (Finset.Icc 1 n)
  rw [countelements]
  --have h := card_I
  rw [← card_Icc_one_n_n n]
  apply card_le_of_subset
  rw [card_Icc_one_n_n n]
  exact filter_subset (· ∈ A) (Finset.Icc 1 n)

  -- exact empty_subset (Finset.filter (· ∈ A) (Finset.Icc 1 n))

#check countelements_nonneg
-- #check Set.inter
#check countelements_le_n

-- #check Real.sInf_nonneg
-- #check Set.range

noncomputable def schnirelmanndensity (A : Set ℕ) : ℝ := ⨅ (n : {n : ℕ // n ≠ 0}), (countelements A n / n)

lemma schnirelmanndensity_nonneg (A : Set ℕ) : (0 ≤ schnirelmanndensity A) := by
  rw [schnirelmanndensity]
    -- have u := countelements_nonneg
  apply Real.iInf_nonneg
  intro i
  -- apply Real.iInf_nonneg
  -- intro h
  have u₀ : 0 ≤ (i : ℝ) := by simp only [Nat.cast_nonneg]
  -- have u₁ : 0 < (1 / i : ℝ) := by simp only [one_div, inv_pos, Nat.cast_pos, u]
  -- have u₂ : 0 ≤ (1 / i : ℝ)  := by simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  have u₁ : 0 ≤ (countelements A i : ℝ ) := by simp only [Nat.cast_nonneg]
  norm_cast
  exact div_nonneg u₁ u₀

#check schnirelmanndensity

#check ciInf_le


lemma schnirelmanndensity_le_one (A : Set ℕ) : (schnirelmanndensity A ≤ 1)  := by
  rw [schnirelmanndensity]
  -- have h : (countelements (A) (1)) / 1 ≤ 1 := by
  --   simp only [Nat.div_one]
  --   exact countelements_le_n A 1
  refine' ciInf_le_of_le ?a _ ?c
  · rw [BddBelow]
    use 0
    refine Iff.mpr mem_lowerBounds ?h.aa
    intro xx
    intro hhh
    simp only [Set.mem_range] at hhh
    rcases hhh with ⟨n, hn⟩
    rw [← hn]
    have u₁ : 0 ≤ (countelements A n : ℝ ) := by simp only [Nat.cast_nonneg]
    have u₀ : 0 ≤ (n : ℝ) := by simp only [Nat.cast_nonneg]
    exact div_nonneg u₁ u₀
  · use 1
    norm_num
  · rw [@Subtype.coe_mk]
    norm_cast
    simp only [div_one, Nat.cast_le_one]
    exact countelements_le_n A 1
    -- have hh : (countelements (A) (1) : ℝ) / 1 ≤ 1 := by
    --   norm_cast at h
    -- exact hh


lemma schnirelmanndensity_le_one_minus_k (A : Set ℕ) (k : ℕ) : ¬ (k ∈ A) → schnirelmanndensity A ≤ (1 - 1 / k) := by
  rw [schnirelmanndensity]
  have hh : ¬ (k ∈ A) → countelements A k ≤ k - 1 := by
    intro u
    have h₀ : (Finset.filter (· ∈ A) (Finset.Icc 1 k)) ⊆ (Finset.Icc 1 (k-1)) := by
      intro x hx
      simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc]
      simp only [gt_iff_lt, Nat.lt_one_iff, mem_Icc, and_imp, mem_filter] at hx
      rcases hx with ⟨⟨ hx₁, hx₂⟩ , hx₃⟩
      constructor
      · exact hx₁
      · by_contra'  hf
        have vv : x = k := by
          refine Eq.symm (Nat.le_antisymm ?h₁ hx₂)
          exact Nat.le_of_pred_lt hf
        apply u
        rw [← vv]
        exact hx₃
    rw [countelements]
    rw [← card_Icc_one_n_n (k-1)]
    apply card_le_of_subset
    apply h₀
  intro hk_not_in_A
  have hk : 0 ≤ (k : ℝ) := by simp only [Nat.cast_nonneg]
  -- have hk' : 0 ≤ 1 / (k : ℝ) := by simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  have u : 0 ≤ (countelements A k : ℝ) := by simp only [Nat.cast_nonneg]
  have udiv : 0 ≤ (countelements A k : ℝ) / k := div_nonneg u hk
  have hc : (countelements A k) ≤ k - 1 := by
    apply hh hk_not_in_A
  rcases k.eq_zero_or_pos with k0 | k1
  · rw [k0]
    norm_cast
    simp only [div_zero, sub_zero, ge_iff_le]
    rw [← schnirelmanndensity]
    exact schnirelmanndensity_le_one A
  · refine' ciInf_le_of_le _ _ _
    · rw [BddBelow]
      use 0
      refine Iff.mpr mem_lowerBounds ?h.aa
      intro xx hh
      rw [@Set.mem_range] at hh
      obtain ⟨y, hy⟩ := hh
      rw [← hy]
      have hy' : 0 ≤ (y : ℝ) := by simp only [ne_eq, Nat.cast_nonneg]
      have hy'' : 0 ≤ (countelements A y : ℝ) := by aesop
      exact div_nonneg hy'' hy'
    · use k
      exact Iff.mp Nat.pos_iff_ne_zero k1
    · rw [@Subtype.coe_mk]
      refine div_le_of_nonneg_of_le_mul hk ?inr.refine'_3.hc ?inr.refine'_3.h
      · simp only [one_div, sub_nonneg]
        have hk₀ : 1 ≤ (k : ℝ) := Iff.mpr Nat.one_le_cast k1
        exact inv_le_one hk₀
      · have hknez : (k : ℝ) ≠ 0 := by positivity
        calc
          countelements A k
            ≤ (k : ℝ) - 1               := ?_
          _ = (k - 1) / k * k           := by rw [div_mul, div_self hknez, div_one]
          _ = (1 - 1 / (k : ℝ)) * k     := by rw [one_sub_div hknez]
        rw [← Nat.cast_pred k1]
        exact_mod_cast hc


lemma schnirelmanndensity_one_notin_A (A : Set ℕ) : ¬ (1 ∈ A) → schnirelmanndensity A = 0 := by
  intro u
  rw [← @abs_nonpos_iff]
  rw [abs_le]
  constructor
  · rw [neg_zero]
    exact schnirelmanndensity_nonneg A
  · have h := schnirelmanndensity_le_one_minus_k A 1
    simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, sub_self] at h
    exact h u

#check Even

lemma schnirelmanndensity_even : schnirelmanndensity (setOf Even) = 0 := by
  apply schnirelmanndensity_one_notin_A
  rw [@Set.mem_def]
  have u : Odd 1 → ¬ Even 1 := by
    rw [@even_iff_exists_two_mul]
    push_neg
    intro h c
    rcases c with hc1 | hc2
    · rw [Nat.mul_zero]
      trivial
    · exact Nat.ne_of_beq_eq_false rfl
  exact u odd_one


lemma schnirelmanndensity_primes : schnirelmanndensity (setOf Prime) = 0 := by
  apply schnirelmanndensity_one_notin_A
  rw [@Set.nmem_setOf_iff]
  exact not_prime_one



open Pointwise

-- variable (A B: Set ℕ)
-- #check A ∩ B
-- -- #check finite.sum.finite A B
-- -- #check A Set.vadd +ᵥ B
-- #check  Set.vadd
-- #check VAdd A B
-- #check A +ᵥ B

-- noncomputable def sumset (A B : Set ℕ) : Set ℕ := {a + b // a ∈ A ∧ b ∈ B}

#check eq_iff_le_not_lt

lemma schnirelmanndensity_eq_one (A : Set ℕ) : schnirelmanndensity A = 1 ↔ Set.univ \ {0} ⊆ A := by
  constructor
  · intro h
    by_contra h'
    rw [@Set.not_subset] at h'
    rcases h' with ⟨k, hk₁, hk₂⟩
    have hk₀ : (k : ℝ) ≥ 0 := by simp only [ge_iff_le, Nat.cast_nonneg]
    simp only [Set.mem_univ, not_true, Set.mem_diff, Set.mem_singleton_iff, true_and] at hk₁
    have u : schnirelmanndensity A ≤ 1 - 1 / k := schnirelmanndensity_le_one_minus_k A k hk₂
    rw [h] at u
    simp only [one_div, le_sub_self_iff, inv_nonpos] at u
    have hk₁' : ¬ (k : ℝ) = 0 := by norm_cast
    apply hk₁'
    have v : (k : ℝ) = 0 := by
      rw [le_antisymm_iff]
      constructor
      · exact u
      · exact hk₀
    exact v
  · intro h
    rw [schnirelmanndensity]
    have u (n : ℕ) : (countelements A n) = (n : ℝ) := by -- (_ : 1 ≤ n)
      have v : card (Finset.Icc 1 n) = (n : ℝ) := by
        norm_cast
        exact card_Icc_one_n_n n
      rw [eq_iff_le_not_lt]
      simp only [Nat.cast_le, Nat.cast_lt, not_lt]
      norm_cast at v
      constructor
      · rw [← v]
        apply card_le_of_subset
        rw [v]
        exact filter_subset (fun x ↦ x ∈ A) (Icc 1 n)
      · rw [countelements]
        rw [← v]
        apply card_le_of_subset
        rw [v]
        intro m
        rw [@mem_Icc]
        intro hm
        rw [@mem_filter]
        constructor
        · rw [@mem_Icc]
          exact hm
        · rw [@Set.subset_def] at h
          apply h
          have hm₀ : m ≠ 0 := by
            rw [← @Nat.pos_iff_ne_zero]
            rcases hm with ⟨hm₁, hm₂⟩
            exact hm₁
          exact Set.mem_diff_of_mem trivial hm₀
    have this : ∀ (n : {n : ℕ // n ≠ 0}), (n : ℝ) ≠ 0 := by aesop
    simp [u, this]
    have v : Nonempty { n : ℕ // ¬n = 0 } := by
      rw [@nonempty_subtype]
      use 1
      trivial
    refine IsGLB.ciInf_eq ?mpr.H
    rw [@isGLB_iff_le_iff]
    intro b
    constructor
    · intro hb
      rw [@mem_lowerBounds]
      rintro x hx
      rw [@Set.mem_range] at hx
      obtain ⟨y, hyx⟩ := hx
      have hy : (y : ℕ) ≠ 0 := y.2
      rw [div_self] at hyx
      · rw [← hyx]
        exact hb
      · rw [@Nat.cast_ne_zero]
        exact hy
    · rw [@mem_lowerBounds]
      rintro hx
      specialize hx 1
      apply hx
      rw [@Set.mem_range]
      use ⟨1, one_ne_zero⟩
      simp



#check le_trans
#check zero_le_one

#check ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
#check exists_lt_of_ciInf_lt

#check lt_trichotomy

lemma sumset_contains_n (A B : Set ℕ) (n : ℕ) :(0 ∈ A) → (0 ∈ B) → countelements A n + countelements B n > n - 1 → n ∈ A + B := by sorry

theorem sum_schnirelmanndensity_ge_one_sumset_nat (A B : Set ℕ) : (0 ∈ A) → (0 ∈ B) → schnirelmanndensity A + schnirelmanndensity B ≥ 1 → Set.univ = A + B := by
  intro hA hB h
  have l := lt_trichotomy (schnirelmanndensity A) 0
  rcases l with l1 | l2 | l3
  · have ulb := schnirelmanndensity_nonneg A
    have v : schnirelmanndensity A ≠ schnirelmanndensity A := by
      refine LT.lt.ne ?h
      exact lt_of_lt_of_le l1 ulb
      -- simp only [ne_eq, not_true]
    contradiction
  · rw [l2] at h
    simp only [zero_add, ge_iff_le] at h
    have uub := schnirelmanndensity_le_one B
    have hb : schnirelmanndensity B = 1 := le_antisymm uub h
    have v := schnirelmanndensity_eq_one B
    have hsub : B ⊆ A + B := by
      intro b hb
      rw [@Set.mem_add]
      use 0
      use b
      simp only [zero_add, and_true]
      constructor
      · exact hA
      · exact hb
    rw [v] at hb
    rw [@Set.Subset.antisymm_iff]
    constructor
    · have u : Set.univ \ {0} ⊆ A + B := le_trans hb hsub
      intro x
      rcases x.eq_zero_or_pos with rfl | hxek
      · intro hzero
        rw [@Set.mem_add]
        use 0
        use 0
      · intro hx
        have hxx : x ∈ Set.univ \ {0} := by
          rw [@Set.mem_diff_singleton]
          constructor
          · exact hx
          · exact Iff.mp Nat.pos_iff_ne_zero hxek
        exact hsub (hb hxx)
    · exact Set.subset_univ (A + B)
  · rw [@Set.Subset.antisymm_iff]
    constructor
    · have u : ∀ n : ℕ, countelements A n + countelements B n ≥ n := by
        intro n
        rcases n.eq_zero_or_pos with hn₀ | hnge₀
        · have v := countelements_nonneg
          -- have vB := countelements_nonneg B 0
          rw [hn₀]
          exact v A 0
        · repeat rw [schnirelmanndensity] at h
          -- rw [div_self (n : ℝ)] at h
          norm_cast at h
          sorry
      have hs := sumset_contains_n
      -- rw [u] at hs
      intro n hn
      apply hs
      · exact hA
      · exact hB
      · simp only [ge_iff_le, gt_iff_lt]
        rw [← Nat.succ_le_iff]
        simp only [ge_iff_le] at u
        rw [Nat.succ_eq_add_one, @Nat.sub_add_eq_max]
        rw [@Nat.max_le]
        constructor
        · exact u n
        · rcases n.eq_zero_or_pos with hnzero | hngezero
          · sorry
          · exact Nat.le_trans hngezero (u n)
    · exact Set.subset_univ (A + B)

-- #check sub_eq_add

#check Finset.Icc 1 0

theorem SchnirelmannTheorem (A B : Set ℕ) : schnirelmanndensity (A + B) ≥  schnirelmanndensity A + schnirelmanndensity B - schnirelmanndensity A * schnirelmanndensity B := by sorry

-- theorem MannTheorem (A B : Set ℕ) : schnirelmanndensity (A + B) ≥  Min 1 (schnirelmanndensity A + schnirelmanndensity B) := by sorry

#check le_antisymm

open Real

-- hints from Bhavik

#check ⨅ (x : ℝ), (x + 1) -- is the Inf of (x + 1) as x ranges over ℝ
#check ⨅ (x : ℝ) (_ : x ≤ 1), x ^ 2 -- is the Inf of x ^ 2 as x ranges over ℝ with x ≤ 1

variable (A : Set ℕ) (n : ℕ) [DecidablePred (· ∈ A)] -- mathlib purposes, this has to be written

#check ((Finset.range n).filter (· ∈ A))
#check Finset.card


#check card_empty
#check card_le_of_subset

#check empty_subset

#check filter_subset
#check Nat.card_Icc


variable (A B: Set ℕ)
#check A + B


      -- -- rw [Mathlib.Tactic.Zify.nat_cast_eq] at hk₁
      -- push_neg at hk₁
      -- push_neg
      -- -- rw [← Nat.cast_le] at hk₁
      -- exact hk₁


      -- have t := card_Icc_one_n_n
      -- rw [@division_def]
      -- rw [mul_inv_eq_iff_eq_mul₀]
      -- simp only [one_mul, Nat.cast_inj]
      -- ??
      --refine Eq.symm (Nat.pred_inj x✝ ?_ ?_)
    -- have u := schnirelmanndensity_nonneg A
    -- have u' := schnirelmanndensity_le_one A
    -- by_contra h'
    -- have v : (schnirelmanndensity A < 1)  := Ne.lt_of_le h' u'
    -- rw [schnirelmanndensity] at v
    -- have hi := exists_lt_of_ciInf_lt
    -- rw? at v2


/- OLD PROOF of SD = 1 iff ...
    refine IsGLB.ciInf_eq ?mpr.H
    rw [@isGLB_iff_le_iff]
    intro b
    rw [@mem_lowerBounds]
    constructor
    · intro hb x hx
      rw [@Set.mem_range] at hx
      rcases hx with ⟨y, hy⟩
      rw [← hy]
      rw [u]
      -- rw [div_self]
      rcases y.eq_zero_or_pos with rfl | hgey
      · simp only [Nat.cast_zero, ne_eq, not_true, div_zero, Real.ciInf_const_zero]
        sorry -- <-- MAIN PROBLEM OCCURS HERE, if we write (_ : 1 ≤ n) in the definition of SchnirelmannDenisty. Because, apparently, writing this does not eliminate the case n ≠ 0
      · rw [div_self]
        · have v : 1 ≤ y := hgey
          rw [@le_iff_eq_or_lt]
          left
          right
          -- rw [IsGLB.ciInf_eq] <-- also in this part, it says that "failed to synthesize instance", even v holds
        · have u : (y : ℝ) > 0 := Iff.mpr Nat.cast_pos hgey
          exact ne_of_gt u
    · intro hx
      apply hx 1
      rw [@Set.mem_range]
      use 1
      norm_cast
      rw [countelements]
      simp only [lt_self_iff_false, Icc_self, mem_singleton, forall_eq, div_one, ciInf_unique, Nat.cast_eq_one]
      rw [← card_singleton 1]
      rw [eq_iff_le_not_lt]
      -- simp only [card_singleton, mem_singleton, forall_eq, Nat.lt_one_iff, card_eq_zero]
      constructor
      · apply card_le_of_subset
        rw [card_singleton 1]
        exact filter_subset (fun x ↦ x ∈ A) {1}
      · push_neg
        apply card_le_of_subset
        rw [card_singleton 1]
        intro m hm
        rw [@mem_singleton] at hm
        rw [@mem_filter]
        constructor
        · exact Iff.mpr mem_singleton hm
        · have v : 1 ∈ Set.univ \ {0} := by trivial
          rw [hm]
          exact h v
-/

/-
      -- rw [add_le_add v v₁]
      -- have w : 1 ≤ i := by sorry  -- MAIN PROBLEM OCCURS HERE: by the definition of schnirelmanndensity, i : ℕ should be taken as i ≥ 1. Unfortunately, LEAN wants me to prove this, which is not given
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
