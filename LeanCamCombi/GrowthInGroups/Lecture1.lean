import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import LeanCamCombi.GrowthInGroups.VerySmallDoubling
import LeanCamCombi.Mathlib.Algebra.Group.Subgroup.Pointwise

open Finset Fintype Group Matrix MulOpposite Real
open scoped Combinatorics.Additive MatrixGroups Pointwise

namespace GrowthInGroups.Lecture1
variable {G : Type*} [Group G] [DecidableEq G] {A X : Finset G} {n : ℕ} {K : ℝ}

lemma card_pow_lt_card_pow_succ_of_pow_ne_closure (hX : X.Nontrivial)
    (hXclosure : (X ^ n : Set G) ≠ Subgroup.closure (X : Set G)) : #(X ^ n) < #(X ^ (n + 1)) := by
  refine (hX.nonempty.card_pow_mono <| Order.le_succ _).lt_of_ne fun h ↦ hXclosure ?_
  dsimp at h
  sorry

lemma card_pow_strictMonoOn (hX : X.Nontrivial) :
    StrictMonoOn (fun n ↦ #(X ^ n))
      {n | (X ^ (n - 1) : Set G) ≠ Subgroup.closure (X : Set G)} := by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn ↦
    card_pow_lt_card_pow_succ_of_pow_ne_closure hX hn
  rintro - - n hn m ⟨-, hmn⟩ hm
  apply hn
  obtain rfl | hm₀ := m.eq_zero_or_pos
  · simp at hm
    rw [← hm]
    rw [eq_comm, coe_set_eq_one, Subgroup.closure_eq_bot_iff] at hm
    cases hX.not_subset_singleton hm
  calc (X : Set G) ^ (n - 1) = X ^ (n - m) * X ^ (m - 1) := by rw [← pow_add]; congr 1; omega
  _ = Subgroup.closure (X : Set G) := by rw [hm, Set.mul_subgroupClosure_pow hX.nonempty.to_set]

lemma card_pow_strictMono (hXclosure : (Subgroup.closure (X : Set G) : Set G).Infinite)
    (hX : X.Nontrivial) : StrictMono fun n ↦ #(X ^ n) := by
  have h n : (X ^ (n - 1) : Set G) ≠ Subgroup.closure (X : Set G) :=
    fun h ↦ by simp [← h, ← coe_pow] at hXclosure
  simpa [h] using card_pow_strictMonoOn hX

/-- The growth of a generating set in an infinite group is at least linear. -/
lemma fact_3_1_1 [Infinite G] (hXgen : Subgroup.closure (X : Set G) = ⊤) (hX : X.Nontrivial) :
    ∀ n, n + 1 ≤ #(X ^ n)
  | 0 => by simp
  | n + 1 => (fact_3_1_1 hXgen hX _).trans_lt <|
    card_pow_strictMono (by simp [hXgen, Set.infinite_univ]) hX n.lt_succ_self

/-- The growth of a set is at most exponential. -/
lemma fact_3_1_2 : #(X ^ n) ≤ #X ^ n := card_pow_le

variable (G) in
/-- A group **has polynomial growth** if any (equivalently, all) of its finite symmetric sets
has polynomial growth. -/
def HasPolynomialGrowth : Prop :=
  ∃ X : Finset G, X⁻¹ = X ∧ Subgroup.closure (X : Set G) = ⊤ ∧ ∃ d, ∀ n ≥ 2, #(X ^ n) ≤ n ^ d

/-- Gromov. -/
lemma theorem_3_2 : HasPolynomialGrowth G ↔ IsVirtuallyNilpotent G := sorry

lemma fact_3_3 [Fintype G] (hn : X ^ n = univ) : log (card G) / log #X ≤ n := by
  obtain rfl | hX := X.eq_empty_or_nonempty
  · simp
  refine div_le_of_le_mul₀ (log_nonneg <| by simpa) (by positivity) ?_
  rw [← log_pow, ← Nat.cast_pow, ← card_univ, ← hn]
  gcongr
  exact card_pow_le

/-- **Babai's conjecture**. -/
lemma conjecture_3_4 :
    ∃ Cᵤ ≥ 0, ∃ dᵤ ≥ 0,
      ∀ {G} [Group G] [IsSimpleGroup G] [Fintype G] [DecidableEq G] (X : Finset G),
        ∃ m : ℕ, m ≤ Cᵤ * log (card G) ^ dᵤ ∧ X ^ m = univ := sorry

-- Not even trying to state the collar lemma

open scoped Classical in
lemma proposition_3_7 :
    ∃ ε > 0, ∀ X : Finset SL(2, ℝ), #(X ^ 2) ≤ 1000 * #X → (∀ M ∈ X, ∀ i j, |M i j| ≤ ε) →
      ∃ A : Subgroup SL(2, ℝ), A.IsCommutative ∧
        ∃ a : Fin 10000000 → SL(2, ℝ), (X : Set SL(2, ℝ)) ⊆ ⋃ i, a i • A := sorry

/-- The **Breuillard-Green-Tao theorem**. -/
lemma theorem_3_8 (hK : 0 ≤ K) :
    ∃ C > 0, ∀ {G} [Group G] [DecidableEq G] (A : Finset G) (hA : σₘ[A] ≤ K),
      ∃ (N : Subgroup G) (D : Subgroup N) (hD : D.Normal),
        upperCentralSeries (N⧸ D) C = ⊤ ∧ ((↑) '' (D : Set N) : Set G) ⊆ (A / A) ^ 4 ∧
          ∃ a : Fin C → G, (A : Set G) ⊆ ⋃ i, a i • N := sorry

open scoped Classical in
/-- Breuillard-Green-Tao, Pyber-Szabo. -/
lemma theorem_3_9 :
    ∃ δ > 0, ∃ ε > 0,
      ∀ k [Field k] [Fintype k] [DecidableEq k] (A : Finset SL(n, k))
        (hAgen : Subgroup.closure (A : Set SL(n, k)) = ⊤),
          #A ^ (1 + δ) ≤ #(A ^ 3) ∨ card SL(n, k) ^ (1 - ε) ≤ #A := sorry

open scoped RightActions in
lemma fact_3_10 (hA : #(A * A) ≤ #A) :
    ∃ H : Subgroup G, ∀ a ∈ A, a • (H : Set G) = A ∧ (H : Set G) <• a = A := by
    -- obtain ⟨x, hx⟩ := hA
    have wtf : ∀ (g b : G) (B : Finset G), (b ∈ B) ↔ (g * b ∈ g • B) := fun g b B ↦ by
      rw [mem_smul_finset]
      simp only [smul_eq_mul, mul_right_inj, exists_eq_right]
    have wtf' : ∀ (g b : G) (B : Set G), (b ∈ B) ↔ (b * g ∈ B <• g) := fun g b B ↦ by
      refine ⟨fun hb ↦ mem_rightCoset g hb, fun hb ↦ Set.smul_mem_smul_set_iff.mp hb⟩

    have hA2 : ∀ (a : G), (a ∈ A) → A * A = a • A := fun a ha ↦
      (fun {α} {s t} hst ↦ (eq_iff_card_ge_of_superset hst).mp) (smul_finset_subset_mul ha) (by simpa)
    have hA2' : ∀ (a : G), (a ∈ A) → A * A = A <• a := fun a ha ↦ by
      have h1 : A <• a ⊆ A * A := op_smul_finset_subset_mul ha
      have h2 : #A = #(A <• a) := Eq.symm (card_smul_finset (op a) A)
      rw [h2] at hA
      exact (eq_iff_card_ge_of_superset h1).mp hA
    have hAcomm : ∀ a ∈ A, a • A = A <• a := fun a ha ↦ by rw [← hA2 a ha, hA2' a ha]
    -- have trInv : ∀ (a : G), (a ∈ A) → a⁻¹ •> (A * A) <• a⁻¹ = a⁻¹ • A :=
    --   fun a ha ↦ by
    --     sorry
    -- have trInv' : ∀ (a : G), (a ∈ A) → a⁻¹ •> (A * A) <• a⁻¹ = A <• a⁻¹ :=
    --   fun a ha ↦ by simp only [op_inv, hA2 a ha, inv_smul_smul]
    -- have normal : ∀ (a : G), (a ∈ A) → a⁻¹ • A = A <• a⁻¹ :=
    --   fun a ha ↦ Eq.trans (trInv a ha).symm (trInv' a ha)
    -- have : ∀ (a b : G), (a ∈ A) → (b ∈ A) → a⁻¹ • A = b⁻¹ • A := by
    --   intros a b ha hb
    --   sorry

    -- have unfold : ∀ (m a : G), (a ∈ m • A) → ∃ g, (g ∈ A) ∧ a = m * g := by
    --   intros m a ha

    --   obtain ⟨c, ⟨hc1, hc2⟩⟩ := ha
    --   refine ⟨c, ⟨hc1, Eq.symm (by simpa only [smul_eq_mul] using hc2)⟩⟩
    -- have unfold' : ∀ (m a : G), (a ∈ (A : Set G) <• m) → ∃ g, (g ∈ A) ∧ a = g * m := by
    --   intros m a ha
    --   obtain ⟨c, ⟨hc1, hc2⟩⟩ := ha
    --   refine ⟨c, ⟨hc1, Eq.symm (by simpa only [smul_eq_mul] using hc2)⟩⟩

    -- let H : Subgroup G := {
    --   carrier := x⁻¹ • A
    --   mul_mem' := by
    --     intros a b ha hb
    --     obtain ⟨g, ⟨hg1, hg2⟩⟩ := unfold x⁻¹ a ha
    --     obtain ⟨g', ⟨hg1', hg2'⟩⟩ := unfold' x⁻¹ b ?_
    --     rw [trInv x hx]
    --     refine ⟨g * g', ?_⟩
    --     sorry
    --   one_mem' := by sorry
    --   inv_mem' := by
    --     intros a ha
    --     sorry
    -- }
    -- exact ⟨H, fun a ha ↦ ⟨leftCoset_mem_leftCoset H ha, rightCoset_mem_rightCoset H ha⟩⟩
    let Hcar := {g : G | g • A = A}
    have smuleq : ∀ (a b : G), (a ∈ A) → (b ∈ A) → a • A = b • A :=
      fun a b ha hb ↦ (hA2 a ha).symm.trans (hA2 b hb)
    have Hcarform : ∀ (a : G), (a ∈ A) → a⁻¹ • A = Hcar := fun a ha ↦ by
      unfold Hcar
      ext x
      refine ⟨?_, fun hx ↦ ?_⟩
      { rintro ⟨a', ha', ha''⟩
        simp only [smul_eq_mul, Set.mem_setOf_eq] at ha'' ⊢
        specialize smuleq a' a ha' ha
        rw [← ha'', MulAction.mul_smul, smuleq, ← MulAction.mul_smul, inv_mul_cancel, one_smul] }
      { simp only [Set.mem_setOf_eq] at hx ⊢
        have : a •> (A <• a⁻¹) = (a •> A) <• a⁻¹ := smul_comm a (op a⁻¹) A
        have : A = a •> (A <• a⁻¹) := by
          rw [this, hAcomm a ha]
          simp only [op_inv, inv_smul_smul]
        rw [this, coe_smul_finset, coe_smul_finset, ← MulAction.mul_smul, inv_mul_cancel, one_smul]
        have : x * a ∈ A := by
          specialize wtf x a A
          rwa [← hx, ← wtf]
        rw [wtf' a]
        simpa only [op_inv, smul_inv_smul, mem_coe] }

    let H : Subgroup G := {
      carrier := Hcar
      mul_mem' := by
        intros a b ha hb
        rw [Set.mem_setOf_eq] at ha hb ⊢
        rw [MulAction.mul_smul a b A, hb, ha]
      one_mem' := by rw [Set.mem_setOf_eq, one_smul]
      inv_mem' := fun x ↦ by
        rw [Set.mem_setOf_eq, inv_smul_eq_iff]
        exact Eq.symm ((fun {α} {s t} ↦ val_inj.mp) (congrArg val x))
    }

    refine ⟨H, fun a ha ↦ ⟨?_, ?_⟩⟩
    { ext x
      refine ⟨?_, fun hx ↦ ?_⟩
      { rintro ⟨h, hh1, hh2⟩
        have hh1 : h ∈ a⁻¹ • A := by
          have : h ∈ Hcar := hh1
          rw [← Hcarform a ha] at this
          exact mem_smul_finset.mpr this
        rw [← hh2]
        have := (wtf a h (a⁻¹ • A)).mp
        simp only [smul_inv_smul, smul_eq_mul, mem_coe] at this ⊢
        exact this hh1 }
      { unfold H
        simp_rw [← Hcarform a ha]
        simp only [Subgroup.coe_set_mk, smul_inv_smul, mem_coe]
        exact hx } }
    { ext x
      refine ⟨?_, fun hx ↦ ?_⟩
      { rintro ⟨h, hh1, hh2⟩
        simp at hh1 hh2 ⊢
        have : h • A = A := hh1
        rw [← this, ← hh2]
        exact (wtf h a A).mp ha }
      { unfold H
        simp only [Subgroup.coe_set_mk]
        rw [← Hcarform a ha, ← coe_smul_finset, ← coe_smul_finset]
        exact mem_coe.mpr (by rwa [smul_comm, ← hAcomm a ha, inv_smul_smul]) } }


open scoped Classical RightActions in
lemma lemma_3_11 (hA : #(A * A) < (3 / 2 : ℚ) * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H),
      (card H : ℚ≥0) < 3 / 2 * #A ∧ ∀ a ∈ A, (A : Set G) ⊆ a • H ∧ a • (H : Set G) = H <• a :=
  very_small_doubling hA

end GrowthInGroups.Lecture1
