import Mathlib.Analysis.InnerProductSpace.Projection
import LeanCamCombi.Book.Chapter11LinesInThePlane.SylvesterGallai
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Lines in the plane and decompositions of graphs : 2 theorems and a graph decomposition

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 11: "Pigeon-hole and double counting".
In this file, we formalize the theorems refered to as
"Theorem 2" and "Theorem 3", as well as the first
graph decomposition theorem, in the corresponding chapter
of the book.


## Structure

- `theorem_2` :
      Attributed to Erdös and de Bruijn.
      If a finite set of points aren't aligned, then the number
      of lines passing through pairs of these points is greater
      then the number of points.

- `line_set` :
      Our definition of the set of lines of a point set for `theorem_2`

- `theorem_3` :
      Attributed to Motzkin or Conway.
      Generalises `theorem_2` to more abstract incidence geometries.

- `clique_decomposition` and `clique_decomposition'` :
      If we decompose a complete graph Kₙ into m cliques different
      from  Kₙ, such that every edge is in a unique clique, then m ≥ n.
      There are two versions, with two different notions of "clique"

-/


/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
-- We work in the same context as in the Sylvester-Gallai file
variable {E : Type} [_inst_1 : NormedAddCommGroup E] [_inst_2 : InnerProductSpace ℝ E]
  [_inst_3 : CompleteSpace E]

open scoped Classical

/-- The set of lines passing through pairs of distinct points of
a finite set of points `P`.
-/
noncomputable def lineSet (P : Finset E) :=
  Finset.image (fun p : ↥P × ↥P => line (p.1 : E) (p.2 : E))
    (-- `.val` failed
      Finset.filter
      (fun p : ↥P × ↥P => p.1 ≠ p.2) Finset.univ)

/-- If the line passing through `u ∈ P` and `v ∈ P` contains no other
points of `P`, then the set of lines of `P\u` is less then that
of `P`
-/
theorem list_set_lemma (P : Finset E) (u v : E) (hu : u ∈ P) (hv : v ∈ P) (unv : u ≠ v)
    (uv_prop : ∀ p : E, p ∈ P → p ≠ u → p ≠ v → p ∉ line u v) :
    (lineSet (P.erase u)).card < (lineSet P).card := by
  apply Finset.card_lt_card
  -- We show that erasing `u` causes line `line u v`
  -- to be erased from the line-set
  rw [Finset.ssubset_iff]
  use line u v
  constructor
  · -- We show that `line u v` isn't in the line set by contradiction,
    -- showing that we may find a 3rd (forbidden) point on `line u v`.
    intro con
    rw [lineSet, Finset.mem_image] at con
    rcases Con with ⟨pair, pair_def, eq⟩
    rw [Finset.mem_filter] at pair_def
    have not_both_v : ↑pair.1 ≠ v ∨ ↑pair.2 ≠ v := by
      by_contra! K
      apply pair_def.2
      rw [Subtype.ext_iff]
      rw [K.1, K.2]
    cases not_both_v
    · apply uv_prop ↑pair.1
      · apply Finset.erase_subset u P
        exact pair.1.Prop
      · apply @Finset.ne_of_mem_erase _ _ P _ _
        exact pair.1.Prop
      · exact not_both_v
      · rw [← Eq]
        apply left_mem_line
    · apply uv_prop ↑pair.2
      · apply Finset.erase_subset u P
        exact pair.2.Prop
      · apply @Finset.ne_of_mem_erase _ _ P _ _
        exact pair.2.Prop
      · exact not_both_v
      · rw [← Eq]
        apply right_mem_line
  -- Technicallities
  · intro l ldef
    rw [Finset.mem_insert] at ldef
    cases ldef
    · rw [ldef, lineSet, Finset.mem_image]
      use(⟨u, hu⟩, ⟨v, hv⟩)
      constructor
      · rw [Finset.mem_filter]
        constructor
        apply Finset.mem_univ
        intro con
        simp only [Subtype.mk_eq_mk] at con
        exact unv Con
      · simp only [eq_self_iff_true, Subtype.coe_mk]
    · rw [lineSet, Finset.mem_image] at *
      rcases ldef with ⟨pair, pair_def, eq⟩
      rw [Finset.mem_filter] at pair_def
      use((⟨pair.1.val, by
              apply Finset.erase_subset u P
              exact pair.1.Prop⟩ :
            ↥P),
          (⟨pair.2.val, by
              apply Finset.erase_subset u P
              exact pair.2.Prop⟩ :
            ↥P))
      constructor
      · rw [Finset.mem_filter]
        constructor
        apply Finset.mem_univ
        intro con
        apply pair_def.2
        rw [Subtype.ext_iff_val] at *
        simp only [Subtype.val_eq_coe] at *
        exact Con
      · simp only [Subtype.coe_mk, Subtype.val_eq_coe]
        exact Eq

/-- Attributed to Erdös and de Bruijn

If a finite set of points aren't aligned, then the number
of lines passing through pairs of these points is greater
then the number of points.
-/
theorem theorem_2 (P : Finset E) (hSG : ¬∃ a b : E, ∀ p ∈ P, p ∈ line a b) :
    P.card ≤ (lineSet P).card := by
  revert hSG
  -- We use strong induction
  apply Finset.strongInductionOn P
  intro S ih hSG_S
  -- We consider `line u v` which contains no other points,
  -- which we obtain from Sylvester-Gallai.
  obtain ⟨u, uS, v, vS, uv_prop⟩ := Sylvester_Gallai S hSG_S
  -- We disjoin cases on whether points are aligned if we deleter `u`
  set T := S.erase u with Tdef
  by_cases aligned : ¬∃ a b : E, ∀ p ∈ T, p ∈ line a b
  · -- If not, we may use the induction hypothesis on `P\u` and
    -- our lemma `list_set_lemma` to conclude
    specialize
      ih T
        (by
          apply Finset.erase_ssubset
          exact uS)
        aligned
    rw [Tdef] at ih
    rw [Finset.card_erase_of_mem uS] at ih
    have bound := list_set_lemma S u v uS vS uv_prop.1 uv_prop.2
    rw [Nat.lt_iff_add_one_le] at bound
    rw [tsub_le_iff_right] at ih
    exact le_trans ih bound
  · -- Otherwise, the points are algined, say on `line a b`
    rw [Classical.not_not] at aligned
    rcases aligned with ⟨a, b, ab_prop⟩
    -- We consider the lines passing through `u`
    set L := Finset.image (fun p : E => line u p) T with Ldef
    -- The line all other points are on isn't part of it
    have : line a b ∉ L := by
      -- Otherwise, all points would be aligned
      by_contra K
      apply hSG_S
      use a
      use b
      intro p pS
      by_cases Q : p ≠ u
      · replace pS := finset.mem_erase.mpr ⟨Q, pS⟩
        rw [← Tdef] at pS
        exact ab_prop p pS
      · rw [not_ne_iff] at Q
        rw [Ldef, Finset.mem_image] at K
        rcases K with ⟨q, qdef, eq_lines⟩
        rw [← eq_lines, Q]
        apply left_mem_line
    -- The number of lines of the "pencil" lower-bounds the
    -- number of lines of the line set
    have that : (insert (line a b) L).card ≤ (lineSet S).card := by
      -- This due to them being a subset of the line set
      apply Finset.card_le_of_subset
      intro l ldef
      rw [Finset.mem_insert] at ldef
      rw [lineSet, Finset.mem_image]
      cases ldef
      · -- For `line a b` we need two points of `P` that represent it
        have Tsize : 2 ≤ T.card := by
          apply_fun Finset.card at Tdef
          nth_rw_rhs 1 [Finset.card_erase_of_mem uS] at Tdef
          linarith [Sylvester_Gallai_condition_fact S hSG_S,
            show 1 ≤ S.card by
              rw [← zero_add 1]
              rw [← Nat.lt_iff_add_one_le]
              rw [Finset.card_pos]
              use u
              exact uS]
        obtain ⟨x, y, xdef, ydef, xny⟩ := pair_of_2_le_card Tsize
        rw [Tdef] at xdef ydef
        use(⟨x, (Finset.erase_subset u S) xdef⟩, ⟨y, (Finset.erase_subset u S) ydef⟩)
        constructor
        · simp only [true_and_iff, Finset.mem_univ, Subtype.mk_eq_mk, Finset.mem_filter]
          apply Subtype.ne_of_val_ne
          simp only [Ne.def]
          exact xny
        · simp only [Subtype.coe_mk]
          rw [← Tdef] at xdef ydef
          rw [← line_rw_of_mem_of_mem xny (ab_prop x xdef) (ab_prop y ydef)]
          exact ldef.symm
      · -- For th others, we just need a lot of rewriting
        rw [Ldef, Finset.mem_image] at ldef
        rcases ldef with ⟨t, tdef, teq⟩
        rw [Tdef] at tdef
        use(⟨u, uS⟩, ⟨t, (Finset.erase_subset u S) tdef⟩)
        constructor
        · rw [Finset.mem_filter]
          constructor
          apply Finset.mem_univ
          simp only [Subtype.mk_eq_mk, Ne.def]
          intro con
          apply Finset.not_mem_erase u S
          nth_rw 1 [Con]
          exact tdef
        · simp only [Subtype.coe_mk]
          exact teq
    -- There are as many lines at the tip of the "pencil" as there
    -- are points alinged on `line a b`.
    have thut : T.card = L.card := by
      -- We let points and lines correspond
      apply Finset.card_congr fun t => fun tdef : t ∈ T => line u t
      -- Mappping condition
      · intro t tdef
        dsimp
        rw [Ldef]
        rw [Finset.mem_image]
        use t
        constructor
        exact tdef
        rfl
      -- Injectivity
      · intro s t sdef tdef st_eq
        dsimp at st_eq
        by_contra K
        have problem_1 := line_rw_of_mem_of_mem K (ab_prop s sdef) (ab_prop t tdef)
        have problem_2 : line u t = line s t := by
          apply line_rw_of_mem_of_mem K
          rw [← st_eq]
          apply right_mem_line
          apply right_mem_line
        apply hSG_S
        use a; use b
        intro p pS
        by_cases Q : p ≠ u
        · replace pS := finset.mem_erase.mpr ⟨Q, pS⟩
          rw [← Tdef] at pS
          exact ab_prop p pS
        · rw [not_ne_iff] at Q
          rw [Q, problem_1, ← problem_2]
          apply left_mem_line
      -- Surjectivity
      · intro l ldef
        rw [Ldef, Finset.mem_image] at ldef
        rcases ldef with ⟨t, tdef, teq⟩
        use t
        constructor
        · dsimp
          exact teq
        · exact tdef
    -- Form here, we do some accounting
    apply_fun Finset.card at Tdef
    nth_rw_rhs 1 [Finset.card_erase_of_mem uS] at Tdef
    rw [Finset.card_insert_of_not_mem this] at that
    rw [← thut, Tdef] at that
    rw [Nat.sub_add_cancel] at that
    · exact that
    · rw [← zero_add 1]
      rw [← Nat.lt_iff_add_one_le]
      rw [Finset.card_pos]
      use u
      exact uS

open Finset

open scoped Classical

-- An alias/shortcut I'd like to see in mathlib
theorem Fintype.univ_filter_eq_card_iff {α : Type} [Fintype α] {p : α → Prop} [DecidablePred p] :
    (univ.filter p).card = Fintype.card α ↔ ∀ x : α, p x := by
  simp [card_eq_iff_eq_univ, filter_eq_self]

/-- In the context of `theorem_3`, we must have `r x < m`,
for it ca be at most `m` and assuming equility is contradictory.
-/
theorem theorem_3_ub {α : Type} [DecidableEq α] {X : Finset α} (hX : 3 ≤ X.card) {m : ℕ}
    {A : Fin m → Finset α} (hA : ∀ i : Fin m, A i ⊂ X)
    (h : ∀ x y, x ∈ X → y ∈ X → x ≠ y → ∃ i, x ∈ A i ∧ y ∈ A i ∧ ∀ j, x ∈ A j ∧ y ∈ A j → j = i)
    (r : ∀ x : α, x ∈ X → ℕ)
    (rdef : r = fun (x : α) (xX : x ∈ X) => (Filter (fun i : Fin m => x ∈ A i) univ).card)
    (hr : ∃ x, ∃ h : x ∈ X, r x h = m) : False := by
  -- This proof is best understood by consulting the figure
  -- in our thesis
  rcases hr with ⟨y, yX, rym⟩
  rw [rdef] at rym
  dsimp at rym
  --rw (fintype.card_fin m) at rym, --fails...
  replace rym := Eq.trans rym (Fintype.card_fin m).symm
  rw [Fintype.univ_filter_eq_card_iff] at rym
  obtain ⟨a, adef⟩ :=
    card_pos.mp
      (show 0 < (X.erase y).card by
        rw [card_erase_of_mem yX]
        linarith [show 1 ≤ X.card by linarith])
  set Aay := Classical.choose (h a y ((erase_subset y X) adef) yX (ne_of_mem_erase adef)) with
    Aay_def
  have Aay_prop := Classical.choose_spec (h a y ((erase_subset y X) adef) yX (ne_of_mem_erase adef))
  rw [← Aay_def] at Aay_prop
  obtain ⟨b, bdef, bprop⟩ := (ssubset_iff_of_subset (subset_of_ssubset (hA Aay))).mp (hA Aay)
  have bny : b ≠ y := by
    intro con
    rw [Con] at bprop
    exact bprop Aay_prop.2.1
  set Aby := Classical.choose (h b y bdef yX bny) with Aby_def
  have Aby_prop := Classical.choose_spec (h b y bdef yX bny)
  rw [← Aby_def] at Aby_prop
  have anb : a ≠ b := by
    intro con
    rw [← Con] at bprop
    exact bprop Aay_prop.1
  set Aab := Classical.choose (h a b ((erase_subset y X) adef) bdef anb) with Aab_def
  have Aab_prop := Classical.choose_spec (h a b ((erase_subset y X) adef) bdef anb)
  rw [← Aab_def] at Aab_prop
  have eq1 := Aay_prop.2.2 Aab ⟨Aab_prop.1, rym Aab⟩
  have eq2 := Aby_prop.2.2 Aab ⟨Aab_prop.2.1, rym Aab⟩
  apply bprop
  rw [← eq1, eq2]
  exact Aby_prop.1

/-- We show the bound `|Aᵢ| ≤ r x for x ∉ Aᵢ` from `theorem_3`.
-/
theorem theorem_3_lb {α : Type} [DecidableEq α] {X : Finset α} (hX : 3 ≤ X.card) {m : ℕ}
    {A : Fin m → Finset α} (hA : ∀ i : Fin m, A i ⊂ X)
    (h : ∀ x y, x ∈ X → y ∈ X → x ≠ y → ∃ i, x ∈ A i ∧ y ∈ A i ∧ ∀ j, x ∈ A j ∧ y ∈ A j → j = i)
    (r : ∀ x : α, x ∈ X → ℕ)
    (rdef : r = fun (x : α) (xX : x ∈ X) => (Filter (fun i : Fin m => x ∈ A i) univ).card) :
    ∀ x ∈ X, ∀ i, x ∉ A i → (A i).card ≤ r x (by assumption) := by
  intro x xX j xnA
  rw [rdef]
  -- We associate to each element of Aⱼ one of the Aₖ
  -- that contains the element and x
  set f := fun y => fun hy : y ∈ A j =>
    Classical.choose
      (h x y xX
        (--((subset_of_ssubset (hA j)) hy) --fails by
          apply subset_of_ssubset (hA j)
          exact hy)
        (by
          intro con
          apply xnA
          rw [Con]
          exact hy)) with
    fdef
  -- We use the set of these Aₖ to make the comparison
  set I := image (fun z : A j => f z.val z.Prop) (A j).attach with Idef
  apply @le_of_eq_of_le _ _ _ I.card _
  · -- We show that the correspondence is a bijection
    apply card_congr f
    -- map
    · intro a ha
      rw [Idef]
      rw [mem_image]
      use⟨a, ha⟩
      constructor
      apply mem_attach
      dsimp
      rfl
    -- Injectivity
    · intro a b adef bdef eq
      simp only [fdef] at eq
      -- We introduc noatation and defining properties:
      set ca :=
        Classical.choose
          (h x a xX
            (by
              apply subset_of_ssubset (hA j)
              exact adef)
            (by
              intro con
              apply xnA
              rw [Con]
              exact adef)) with
        cadef
      have Ca :=
        Classical.choose_spec
          (h x a xX
            (by
              apply subset_of_ssubset (hA j)
              exact adef)
            (by
              intro con
              apply xnA
              rw [Con]
              exact adef))
      set cb :=
        Classical.choose
          (h x b xX
            (by
              apply subset_of_ssubset (hA j)
              exact bdef)
            (by
              intro con
              apply xnA
              rw [Con]
              exact bdef)) with
        cbdef
      have Cb :=
        Classical.choose_spec
          (h x b xX
            (by
              apply subset_of_ssubset (hA j)
              exact bdef)
            (by
              intro con
              apply xnA
              rw [Con]
              exact bdef))
      -- If `a ≠ b`, we would get on more Aₖ containg this pair,
      -- which by uniquness of of the sets containing a given pair
      -- must be Aⱼ
      by_contra con
      set cab :=
        Classical.choose
          (h a b
            (by
              apply subset_of_ssubset (hA j)
              exact adef)
            (by
              apply subset_of_ssubset (hA j)
              exact bdef)
            Con) with
        cabdef
      have Cab :=
        Classical.choose_spec
          (h a b
            (by
              apply subset_of_ssubset (hA j)
              exact adef)
            (by
              apply subset_of_ssubset (hA j)
              exact bdef)
            Con)
      rw [← cadef] at *
      rw [← cbdef] at *
      rw [← cabdef] at *
      -- By the injectity assumption `eq` and uniqness of the sets
      -- containing a given pair, A ca and A cb are the same set,
      -- wich contains x and the pair a b, so that these sets must
      -- coinicide with A j, whcih contradicts x ∉ A j.
      apply xnA
      rw [Eq] at Ca
      rw [Cab.2.2 j ⟨adef, bdef⟩]
      rw [← Cab.2.2 cb ⟨Ca.2.1, Cb.2.1⟩]
      exact Cb.1
    -- Surjectivity
    · intro b bI
      rw [Idef, mem_image] at bI
      rcases bI with ⟨c, cdef, ceq⟩
      use c.val; use c.prop
      exact ceq
  · -- We obtain this bound from the sets being subsets,
    -- as all sets of I contain x by definition
    dsimp
    apply card_le_of_subset
    rw [Idef]
    intro i idef
    rw [mem_filter]
    constructor
    apply mem_univ
    rw [mem_image] at idef
    rcases idef with ⟨c, cdef, ceq⟩
    rw [fdef] at ceq
    dsimp at ceq
    rw [← ceq]
    exact
      (Classical.choose_spec
          (h x (↑c) xX
            (by
              apply subset_of_ssubset (hA j)
              exact c.prop)
            (by
              intro con
              apply xnA
              rw [Con]
              exact c.prop))).1

open scoped BigOperators

/-- An algeraic rewrite-/
theorem splitter {α : Type} [DecidableEq α] (X : Finset α) (hX : 0 < X.card) :
    (1 : ℚ) = ∑ x in X, (1 / X.card : ℚ) := by
  have : (X.card : ℚ) ≠ 0 := by
    intro con
    rw [Nat.cast_eq_zero] at con
    rw [Con] at hX
    exact (lt_irrefl 0) hX
  nth_rw 1 [← mul_one_div_cancel this]
  nth_rw 1 [card_eq_sum_ones X]
  push_cast
  rw [zero_add]
  --rw @sum_div _ _ _ X (λ y, (1 : ℚ)) (X.card : ℚ), --fails
  simp only [one_div, mul_eq_mul_left_iff, Finset.sum_const, Finset.card_eq_zero, nsmul_eq_mul,
    true_or_iff, eq_self_iff_true, Nat.cast_inj, inv_inj, Nat.cast_eq_zero, Finset.sum_congr,
    Nat.smul_one_eq_coe]

-- An alias/shortcut I'd like to see in mathlib
theorem sum_rel {α β : Type} [DecidableEq α] [DecidableEq β] (X : Finset α) (U : Finset β)
    (r : α → β → Prop) {hr : ∀ x : α, ∀ y : β, Decidable (r x y)} (f : α → β → ℚ) :
    ∑ x in X, ∑ i in U.filter fun i => r x i, f x i =
      ∑ i in U, ∑ x in X.filter fun x => r x i, f x i := by
  simp_rw [sum_filter]
  rw [sum_comm]

/-- Attributed to Motzkin or Conway

Generalises `theorem_2` to more abstract incidence geometries.
-/
theorem theorem_3 {α : Type} [DecidableEq α] (X : Finset α) (hX : 3 ≤ X.card) (m : ℕ) (hm : 0 < m)
    (A : Fin m → Finset α) (hA : ∀ i : Fin m, A i ⊂ X)
    (h : ∀ x y, x ∈ X → y ∈ X → x ≠ y → ∃ i, x ∈ A i ∧ y ∈ A i ∧ ∀ j, x ∈ A j ∧ y ∈ A j → j = i) :
    X.card ≤ m := by
  -- We deinie the number of appearance of an x in the sets Aᵢ
  set r := fun x : α => fun xX : x ∈ X => (univ.filter fun i => x ∈ A i).card with rdef
  -- We derive r x < m
  by_cases Q : ∃ x, ∃ h : x ∈ X, r x h = m
  · exfalso
    apply theorem_3_ub hX hA h r rdef Q
  · push_neg at Q
    -- We have r x ≤ m via subsets, so that in our case:
    replace Q : ∀ (x : α) (h : x ∈ X), r x h < m := by
      intro x xdef
      apply lt_of_le_of_ne _ (Q x xdef)
      rw [rdef]
      dsimp
      --rw ← (fintype.card_fin m), --fails
      convert card_filter_le univ fun i : Fin m => x ∈ A i
      rw [card_univ]
      rw [Fintype.card_fin m]
    -- we recall our previously derived bound
    have lb := theorem_3_lb hX hA h r rdef
    by_contra! con
    -- We set up the main bound that will yield a contradiction
    -- from some algebraic manipulations
    have bound :
      ∀ x ∈ X,
        ∀ i,
          x ∉ A i →
            (1 / (m * (X.card - (A i).card)) : ℚ) <
              (1 / (X.card * (m - r x (by assumption))) : ℚ) := by
      intro x hx i xnA
      apply div_lt_div' (le_refl (1 : ℚ)) _ (by norm_num)
      · apply mul_pos
        rw [Nat.cast_pos]
        exact lt_trans hm Con
        rw [sub_pos]
        rw [Nat.cast_lt]
        exact Q x hx
      · rw [mul_sub, mul_sub]
        rw [mul_comm]
        rw [sub_lt_sub_iff_left]
        apply mul_lt_mul_of_nonneg_of_pos
        · rw [Nat.cast_lt]
          exact Con
        · rw [Nat.cast_le]
          apply lb x hx i xnA
        · apply Nat.cast_nonneg
        · rw [Nat.cast_pos]
          simp only [rdef]
          rw [card_pos]
          obtain ⟨a, adef⟩ :=
            card_pos.mp
              (show 0 < (X.erase x).card by
                rw [card_erase_of_mem hx]
                linarith [show 1 ≤ X.card by linarith])
          use Classical.choose (h a x ((erase_subset x X) adef) hx (ne_of_mem_erase adef))
          rw [mem_filter]
          constructor
          apply mem_univ
          exact
            (Classical.choose_spec (h a x ((erase_subset x X) adef) hx (ne_of_mem_erase adef))).2.1
    -- We contradiciton will stem from 1<1, via so rewrites and `bound`
    apply lt_irrefl (1 : ℚ)
    nth_rw 2 [splitter X (by linarith)]
    nth_rw 1 [splitter (univ : Finset (Fin m)) (by rw [card_univ, Fintype.card_fin]; exact hm)]
    have rw_left :
      ∑ x in X, (1 / X.card : ℚ) =
        ∑ x in X.attach,
          ∑ i in univ.filter fun i => ↑x ∉ A i,
            (1 / (X.card * (m - r (↑x) x.Prop)) : ℚ) :=-- Note: we need an `attach` to define r by
      rw [← sum_attach]
      apply sum_congr
      rfl
      intro x xX
      rw [← one_div_mul_one_div]
      rw [← mul_sum]
      nth_rw 1 [← mul_one (1 / X.card : ℚ)]
      rw [mul_eq_mul_left_iff]
      left
      have : 0 < (univ.filter fun i => ↑x ∉ A i).card := by
        rw [card_pos]
        by_contra! K
        rw [Finset.Nonempty] at K
        push_neg at K
        apply theorem_3_ub hX hA h r rdef
        use↑x; use x.prop
        rw [rdef]
        dsimp
        --rw ← (fintype.card_fin m), --fails
        have : (univ.filter fun i => ↑x ∈ A i) = univ := by
          rw [filter_eq_self]
          intro y yu
          by_contra! ycon
          apply K y
          rw [mem_filter]
          constructor
          exact yu
          exact ycon
        rw [this]
        rw [card_univ, Fintype.card_fin]
      nth_rw 1 [splitter (univ.filter fun i => ↑x ∉ A i) this]
      clear this
      have : (univ.filter fun i => ↑x ∉ A i).card = m - r (↑x) x.prop := by
        rw [← compl_filter]
        rw [card_compl]
        rw [rdef, Fintype.card_fin]
      rw [this]
      rw [Nat.cast_sub]
      exact le_of_lt (Q (↑x) x.prop)
    rw [rw_left]
    clear rw_left
    have rw_right :
      ∑ i : Fin m, 1 / ((univ : Finset (Fin m)).card : ℚ) =
        ∑ i : Fin m,
          ∑ x in X.attach.filter fun x => ↑x ∉ A i, (1 / (m * (X.card - (A i).card)) : ℚ) := by
      apply sum_congr
      rfl
      intro i iu
      rw [← one_div_mul_one_div]
      rw [← mul_sum]
      nth_rw 1 [← mul_one (1 / univ.card : ℚ)]
      rw [card_univ, Fintype.card_fin]
      rw [mul_eq_mul_left_iff]
      left
      have : 0 < (X.attach.filter fun x => ↑x ∉ A i).card := by
        rw [card_pos]
        obtain ⟨y, ynA, ymem⟩ := ssubset_iff.mp (hA i)
        use⟨y, ymem (mem_insert_self y (A i))⟩
        rw [mem_filter]
        constructor
        apply mem_attach
        simp only [Subtype.coe_mk]
        exact ynA
      nth_rw 1 [splitter (X.attach.filter fun x => ↑x ∉ A i) this]
      clear this
      have : (X.attach.filter fun x => ↑x ∉ A i).card = X.card - (A i).card := by
        rw [filter_not]
        rw [← card_sdiff (subset_of_ssubset (hA i))]
        nth_rw 1 [←
          show X ∩ A i = A i by
            rw [inter_eq_right_iff_subset]
            exact subset_of_ssubset (hA i)]
        rw [← filter_mem_eq_inter]
        rw [eq_comm]
        apply
          card_congr fun x => fun hx : x ∈ X \ Filter (fun j : α => j ∈ A i) X =>
            (⟨x, (sdiff_subset X (Filter (fun j : α => j ∈ A i) X)) hx⟩ : { x // x ∈ X })
        -- map
        · intro a adef
          dsimp
          rw [mem_sdiff]
          constructor
          apply mem_attach
          intro K
          rw [mem_filter] at K
          rw [mem_sdiff] at adef
          apply adef.2
          rw [mem_filter]
          rw [Subtype.coe_mk] at K
          exact ⟨adef.1, K.2⟩
        -- inj
        · intro a b adef bdef eq
          dsimp at eq
          rw [Subtype.mk_eq_mk] at eq
          exact Eq
        -- surj
        · intro b bdef
          use↑b
          have : ↑b ∈ X \ Filter (fun j : α => j ∈ A i) X := by
            rw [mem_sdiff]
            rw [mem_sdiff] at bdef
            constructor
            exact b.prop
            rw [mem_filter]
            rw [mem_filter] at bdef
            intro K
            apply bdef.2
            exact ⟨mem_attach X b, K.2⟩
          use this
          simp only [eq_self_iff_true, Finset.mk_coe]
      rw [this]
      rw [Nat.cast_sub]
      exact card_le_of_subset (subset_of_ssubset (hA i))
    rw [rw_right]
    clear rw_right
    -- To make the comparison, we first swap sums:
    have :=
      sum_rel X.attach (univ : Finset (Fin m)) (fun x => fun i => ↑x ∉ A i) fun x => fun i =>
        (1 / (X.card * (m - r (↑x) x.Prop)) : ℚ)
    dsimp at this
    rw [this]
    -- Then we compare sums, which due to < requires showing
    -- non-emptyness of index sets
    apply sum_lt_sum_of_nonempty
    · exact @univ_nonempty _ _ (fin.pos_iff_nonempty.mp hm)
    intro i idef
    apply sum_lt_sum_of_nonempty
    · obtain ⟨y, ynA, ymem⟩ := ssubset_iff.mp (hA i)
      use y
      exact ymem (mem_insert_self y (A i))
      rw [mem_filter]
      constructor
      apply mem_attach
      exact ynA
    -- In this second comparision, we make use of `bound`
    intro x xdef
    rw [mem_filter] at xdef
    exact bound (↑x) x.prop i xdef.2

open SimpleGraph

/-- If we decompose a complete graph Kₙ into m cliques different
from  Kₙ, such that every edge is in a unique clique, then m ≥ n.

This is a first verison, with a direct definition of cliques
-/
theorem clique_decomposition {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (hV : 3 ≤ Fintype.card V) (hm : 0 < m) (D : Fin m → Subgraph (completeGraph V))
    (hD_1 : ∀ i : Fin m, (D i).verts.toFinset ⊂ (univ : Finset V))
    --(hD_2 : ∀ i : fin m, (subgraph.coe (D i)) = complete_graph ↥(D i).verts) -- bad (?) formalisation
    (hD_2 :
      ∀ i : Fin m,
        (Subgraph.spanningCoe (D i)).Adj = fun x y =>
          if x ∉ (D i).verts ∨ y ∉ (D i).verts then False else x ≠ y)
    (h :
      ∀ e,
        e ∈ (completeGraph V).edgeFinset →
          ∃ i,
            e ∈ edgeFinset (Subgraph.spanningCoe (D i)) ∧
              ∀ j, e ∈ edgeFinset (Subgraph.spanningCoe (D j)) → j = i) :
    Fintype.card V ≤ m := by
  rw [← card_univ]
  rw [← card_univ] at hV
  -- We apply `theorem_3` on the vertices,
  -- where Aᵢ is the vertex set of clique i
  set A := fun i : Fin m => (D i).verts.toFinset with Adef
  replace hD_1 : ∀ i, A i ⊂ univ := by
    intro i
    simp only [Adef]
    exact hD_1 i
  apply theorem_3 (univ : Finset V) hV m hm A hD_1
  intro x y xu yu xny
  specialize h ⟦(x, y)⟧ _
  · rw [mem_edge_finset, mem_edge_set]
    dsimp [completeGraph]
    exact xny
  rcases h with ⟨i, i_prop, i_uni⟩
  use i
  constructor
  · rw [mem_edge_finset, mem_edge_set] at i_prop
    replace i_prop := (D i).edge_vert i_prop
    simp only [Adef]
    rw [Set.mem_toFinset]
    exact i_prop
  constructor
  · rw [mem_edge_finset, mem_edge_set] at i_prop
    replace i_prop := (D i).edge_vert (adj.symm i_prop)
    simp only [Adef]
    rw [Set.mem_toFinset]
    exact i_prop
  · intro j j_prop
    apply i_uni j
    rw [mem_edge_finset, mem_edge_set]
    simp only [Adef, Set.mem_toFinset] at j_prop
    simp only [hD_2 j]
    rw [if_neg _]
    exact xny
    push_neg
    exact j_prop

/-- If we decompose a complete graph Kₙ into m cliques different
from  Kₙ, such that every edge is in a unique clique, then m ≥ n.

This is a second version, with the mathlib notion of cliques
-/
theorem clique_decomposition' {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (hV : 3 ≤ Fintype.card V) (hm : 0 < m) (D : Fin m → Subgraph (completeGraph V))
    (hD_1 : ∀ i : Fin m, (D i).verts.toFinset ⊂ (univ : Finset V))
    (hD_2 : ∀ i : Fin m, IsClique (Subgraph.spanningCoe (D i)) (D i).verts)
    (h :
      ∀ e,
        e ∈ (completeGraph V).edgeFinset →
          ∃ i,
            e ∈ edgeFinset (Subgraph.spanningCoe (D i)) ∧
              ∀ j, e ∈ edgeFinset (Subgraph.spanningCoe (D j)) → j = i) :
    Fintype.card V ≤ m := by
  rw [← card_univ]
  rw [← card_univ] at hV
  set A := fun i : Fin m => (D i).verts.toFinset with Adef
  replace hD_1 : ∀ i, A i ⊂ univ := by
    intro i
    simp only [Adef]
    exact hD_1 i
  apply theorem_3 (univ : Finset V) hV m hm A hD_1
  intro x y xu yu xny
  specialize h ⟦(x, y)⟧ _
  · rw [mem_edge_finset, mem_edge_set]
    dsimp [completeGraph]
    exact xny
  rcases h with ⟨i, i_prop, i_uni⟩
  use i
  constructor
  · rw [mem_edge_finset, mem_edge_set] at i_prop
    replace i_prop := (D i).edge_vert i_prop
    simp only [Adef]
    rw [Set.mem_toFinset]
    exact i_prop
  constructor
  · rw [mem_edge_finset, mem_edge_set] at i_prop
    replace i_prop := (D i).edge_vert (adj.symm i_prop)
    simp only [Adef]
    rw [Set.mem_toFinset]
    exact i_prop
  -- merely this code block differs from the previous proof
  intro j j_prop
  apply i_uni j
  rw [mem_edge_finset, mem_edge_set]
  simp only [Adef, Set.mem_toFinset] at j_prop
  specialize hD_2 j
  rw [is_clique_iff] at hD_2
  specialize hD_2 j_prop.1 j_prop.2 xny
  exact hD_2
