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
open Function

noncomputable def countelements (A : Set ℕ) (n : ℕ) : ℕ := -- for teaching purposes,
  Finset.card ((Icc 1 n).filter (· ∈ A))      -- writing this is better

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
    use n, 0
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
        set f := fun x ↦ n - x
        have hfinj : Set.InjOn f (filter (fun x ↦ x ∈ B) (Icc 1 (n - 1))) := by -- (filter (fun x ↦ x ∈ B) (Icc 1 (n - 1)))
          intro xx hxx yy hyy hfxy
          simp only [ge_iff_le] at hfxy
          simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp,
            coe_filter, Set.mem_setOf_eq] at hxx
          simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp,
            coe_filter, Set.mem_setOf_eq] at hyy
          have hnx : 0 < n - xx := by
            obtain ⟨hx1, hx2⟩ := hxx
            obtain ⟨hx11, hx12⟩ := hx1
            rw [← Nat.lt_add_one_iff] at hx12
            have : n - 1 + 1 = n := by
              zify
              aesop
            rw [this] at hx12
            rwa [tsub_pos_iff_lt]
          have hny : 0 < n - yy := by
            obtain ⟨hy1, hy2⟩ := hyy
            obtain ⟨hy11, hy12⟩ := hy1
            rw [← Nat.lt_add_one_iff] at hy12
            have : n - 1 + 1 = n := by
              zify
              aesop
            rw [this] at hy12
            rwa [tsub_pos_iff_lt]
          zify at hfxy
          rw [Nat.cast_sub, Nat.cast_sub] at hfxy
          · simp at hfxy
            exact hfxy
          · by_contra! hny0
            have : n - yy = 0 := by
                have hhle : n ≤ yy := Nat.le_of_lt hny0
                rw [Nat.sub_eq_zero_of_le hhle]
            rw [this] at hny
            absurd hny
            trivial
          · by_contra! hnx0
            have : n - xx = 0 := by
                have hhle : n ≤ xx := Nat.le_of_lt hnx0
                rw [Nat.sub_eq_zero_of_le hhle]
            rw [this] at hnx
            absurd hnx
            trivial
        have hfim : Finset.image f (filter (fun x ↦ x ∈ B) (Icc 1 (n - 1))) = (filter (fun x ↦ x ∈ {n} - B) (Icc 1 (n - 1))) := by
          ext y
          constructor
          · intro hy
            simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp,
              mem_image, mem_filter] at hy
            simp only [Set.singleton_sub, ge_iff_le, Set.mem_image, gt_iff_lt, Nat.lt_one_iff,
              tsub_eq_zero_iff_le, mem_Icc, and_imp, not_exists, not_and, mem_filter]
            obtain ⟨a, hya, hnay⟩ := hy
            obtain ⟨hya1, hya2⟩ := hya
            obtain ⟨hya11, hya12⟩ := hya1
            constructor
            · constructor
              · rw [← hnay]
                rw [← Nat.lt_add_one_iff] at hya12
                have : n - 1 + 1 = n := by
                  zify
                  aesop
                rw [this] at hya12
                -- zify
                rw [Nat.one_le_iff_ne_zero]
                exact Nat.sub_ne_zero_of_lt hya12
              · rw [← hnay, ← Nat.lt_add_one_iff]
                have : n - 1 + 1 = n := by
                  zify
                  aesop
                rw [this, tsub_lt_iff_right]
                zify
                · simp only [lt_add_iff_pos_right, Nat.cast_pos]
                  exact hya11
                · rw [← Nat.lt_add_one_iff, this] at hya12
                  exact Nat.le_of_lt hya12
            · use a
          · intro hy
            simp only [Set.singleton_sub, ge_iff_le, Set.mem_image, gt_iff_lt, Nat.lt_one_iff,
              tsub_eq_zero_iff_le, mem_Icc, and_imp, not_exists, not_and, mem_filter] at hy
            simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp,
              mem_image, mem_filter]
            obtain ⟨hy1, x, hnxy⟩ := hy
            obtain ⟨hy11, hy12⟩ := hy1
            obtain ⟨hx, hnxy1⟩ := hnxy
            use x
            constructor
            · constructor
              · constructor
                · rw [← hnxy1, ← Nat.lt_add_one_iff] at hy12
                  have : n - 1 + 1 = n := by
                    zify
                    aesop
                  rw [this, tsub_lt_iff_right] at hy12
                  zify at hy12
                  · simp only [lt_add_iff_pos_right, Nat.cast_pos] at hy12
                    exact hy12
                  · rw [← hnxy1] at hy11
                    by_contra! hnx
                    have last : n - x = 0 := by
                      have hhle : n ≤ x := Nat.le_of_lt hnx
                      rw [Nat.sub_eq_zero_of_le hhle]
                    rw [last] at hy11
                    absurd hy11
                    trivial
                · rw [← hnxy1] at hy11
                  by_contra! hnx
                  have last : n - x ≤ 0 := by
                    rw [← Nat.add_one_le_iff] at hnx
                    have : n - 1 + 1 = n := by
                      zify
                      aesop
                    rw [this] at hnx
                    rw [Nat.sub_eq_zero_of_le hnx]
                  have abs : 1 ≤ 0 := le_trans hy11 last
                  absurd abs
                  trivial
              · exact hx
            · exact hnxy1
        rw [← hfim]
        exact card_image_iff.mpr hfinj
      have lem2 : (Icc 1 (n-1)).filter (· ∈ A) ∪ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1))) ⊆ Icc 1 (n-1) := by
        intro x hx
        simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp,
          Set.singleton_sub, Set.mem_image, not_exists, not_and, mem_union, mem_filter] at hx
        simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc]
        rcases hx with hx1 | hx2
        · exact hx1.1
        · exact hx2.1
      have lem3 : (Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1))) ≠ ∅ := by
        rw [← hca, ← hcb] at hc
        have hun : Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∪ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) ≤ n - 1 := by
          nth_rewrite 3 [← card_Icc_one_n_n (n - 1)]
          exact card_le_of_subset lem2
        have hui : Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∪ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1))))
          + Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) = countelements A (n-1) + countelements B (n-1) := by
            rw [card_union_add_card_inter, ← lem1, countelements]
        have hin : 0 < Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) := by
          rw [← hui] at hc
          -- have hip : 0 ≤ Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) := by positivity
          have hun1 : Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∪ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1))))
            + Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) ≤ (n - 1)
            + Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) := add_le_add hun le_rfl
          have hip0 : n ≤ (n - 1) + Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) := le_trans hc hun1
          by_contra! hip
          have hip1 : (n - 1) + Finset.card ((Icc 1 (n-1)).filter (· ∈ A) ∩ (Finset.filter (· ∈ {n} - B) (Icc 1 (n-1)))) ≤ (n - 1) := add_le_add le_rfl hip
          have hnn : n ≤ (n - 1) := le_trans hip0 hip1
          rw [← not_lt] at hnn
          apply hnn
          rw [propext (Nat.lt_iff_le_pred hn1)]
        rwa [← Finset.nonempty_iff_ne_empty, ← Finset.card_pos]
      simp only [Nat.lt_one_iff, tsub_eq_zero_iff_le, mem_Icc, and_imp, Set.singleton_sub, Set.mem_image, ne_eq] at lem3  -- set is nonempty iff ?
      have lem31 : A ∩ ({n} - B) ∩ Icc 1 (n-1) ≠ ∅ := by
        intro hyp
        apply lem3
        rw [← filter_and, filter_eq_empty_iff]
        intro xx hxx
        push_neg
        intro hxa yy hyb
        intro main
        have : xx ∈ A ∩ ({n} - B) ∩ Icc 1 (n-1) := by
          constructor
          · constructor
            · exact hxa
            · rw [Set.mem_sub]
              use n, yy
              constructor
              · rfl
              · constructor
                · exact hyb
                · exact main
          · exact hxx
        rw [hyp] at this
        contradiction
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
          have : yy = n - x := by
            zify
            rw [Nat.cast_sub, eq_sub_iff_add_eq', ← eq_sub_iff_add_eq, ← Nat.cast_sub]
            · exact id hxy.symm
            · simp only [ge_iff_le, Nat.cast_inj] at hxy
              rw [← hxy] at hx2
              simp only [ge_iff_le, gt_iff_lt, Nat.lt_one_iff, tsub_eq_zero_iff_le, coe_Icc, not_le,
                Set.mem_Icc, tsub_le_iff_right] at hx2
              zify at hx2
              by_contra! hh
              have : n - yy = 0 := by
                have hhle : n ≤ yy := Nat.le_of_lt hh
                rw [Nat.sub_eq_zero_of_le hhle]
              rw [this] at hx2
              obtain ⟨hx21, hx22⟩ := hx2
              rw [← Int.not_lt] at hx21
              apply hx21
              simp only [Nat.cast_zero, zero_lt_one]
            · exact Nat.le_of_lt hnx
          rwa [← this]
        aesop
    apply h
    obtain ⟨aa, bb, haa, hbb, hnn⟩ := main
    rw [eq_sub_iff_add_eq] at hnn
    rw [Set.mem_add]
    use aa, bb
    constructor
    · exact haa
    · constructor
      · exact hbb
      · zify
        exact hnn



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