/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Function
import LeanCamCombi.Mathlib.Algebra.Order.Monovary
import LeanCamCombi.Mathlib.Algebra.Order.SMul

/-!
# Product of convex functions
-/

open Set

variable {𝕜 E F : Type*} [LinearOrderedCommRing 𝕜] [LinearOrderedCommRing E]
  [LinearOrderedAddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] [Module E F] [IsScalarTower 𝕜 E F]
  [SMulCommClass 𝕜 E F] [OrderedSMul 𝕜 E] [OrderedSMul 𝕜 F] [OrderedSMul E F] {s : Set 𝕜}
  {f : 𝕜 → E} {g : 𝕜 → F}

lemma ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (hg₀ $ hf.1 hx hy ha hb hab) $
    add_nonneg (smul_nonneg ha $ hf₀ hx) $ smul_nonneg hb $ hf₀ hy).trans ?_
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x)
        := ?_
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y)
        := add_le_add_left (smul_le_smul_of_nonneg (hfg.smul_add_smul_le_smul_add_smul hx hy) $
            mul_nonneg ha hb) _
    _ = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y)
        := by simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ = _ := by simp_rw [hab, mul_one]
  simp only [mul_add, add_smul, smul_add]
  rw [←smul_smul_smul_comm a, ←smul_smul_smul_comm b, ←smul_smul_smul_comm a b,
    ←smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b,
    add_comm _ ((b * b) • f y • g y), add_add_add_comm, add_comm ((a * b) • f y • g x)]

lemma ConcaveOn.smul' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (add_nonneg
    (smul_nonneg ha $ hg₀ hx) $ smul_nonneg hb $ hg₀ hy) $ hf₀ $ hf.1 hx hy ha hb hab).trans' ?_
  calc a • f x • g x + b • f y • g y
        = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y)
        := by simp_rw [hab, mul_one]
    _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y)
        := by simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x)
        := add_le_add_left (smul_le_smul_of_nonneg (hfg.smul_add_smul_le_smul_add_smul hx hy) $
            mul_nonneg ha hb) _
    _ = _ := ?_
  simp only [mul_add, add_smul, smul_add]
  rw [←smul_smul_smul_comm a, ←smul_smul_smul_comm b, ←smul_smul_smul_comm a b,
    ←smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b a,
    add_comm ((a * b) • f x • g y), add_comm ((a * b) • f x • g y), add_add_add_comm]

lemma ConvexOn.smul'' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g) := by
  rw [←neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 $ hf₀ hx) (fun x hx ↦ neg_nonneg.2 $ hg₀ hx) hfg.neg

lemma ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  rw [←neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 $ hf₀ hx) (fun x hx ↦ neg_nonneg.2 $ hg₀ hx)
    hfg.neg

lemma ConvexOn.smul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [←neg_convexOn_iff, ←smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 $ hg₀ hx) hfg.neg_right

lemma ConcaveOn.smul_convexOn (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [←neg_concaveOn_iff, ←smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 $ hg₀ hx) hfg.neg_right

lemma ConvexOn.smul_concaveOn' (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [←neg_concaveOn_iff, ←smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 $ hg₀ hx) hfg.neg_right

lemma ConcaveOn.smul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [←neg_convexOn_iff, ←smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 $ hg₀ hx) hfg.neg_right

variable [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] {f g : 𝕜 → E}

lemma ConvexOn.mul (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg

lemma ConvexOn.mul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg

lemma ConvexOn.mul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul_concaveOn hg hf₀ hg₀ hfg

lemma ConcaveOn.mul_convexOn (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_convexOn hg hf₀ hg₀ hfg

lemma ConvexOn.mul_concaveOn' (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_concaveOn' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := hf.smul_convexOn' hg hf₀ hg₀ hfg

lemma ConvexOn.pow (hf : ConvexOn 𝕜 s f) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) :
    ∀ n, ConvexOn 𝕜 s (f ^ n)
  | 0 => by simpa using convexOn_const 1 hf.1
  | n + 1 => by rw [pow_succ]; exact hf.mul (hf.pow hf₀ _) hf₀ (fun x hx ↦ pow_nonneg (hf₀ hx) _) $
      (monovaryOn_self f s).pow_right₀ hf₀ n

-- TODO: Replace `convexOn_pow`
lemma convexOn_pow' : ∀ n, ConvexOn 𝕜 (Ici 0) (fun x : 𝕜 ↦ x ^ n) :=
  (convexOn_id $ convex_Ici _).pow fun _ ↦ id
