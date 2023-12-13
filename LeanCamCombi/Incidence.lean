/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Module.BigOperators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Pi
import Mathlib.Data.Finset.LocallyFinite

/-!
# Incidence algebras

Given a locally finite order `α` the incidence algebra over `α` is the type of functions from
non-empty intervals of `α` to some algebraic codomain.
This algebra has a natural multiplication operation whereby the product of two such functions
is defined on an interval by summing over all divisions into two subintervals the product of the
values of the original pair of functions.
This structure allows us to interpret many natural invariants of the intervals (such as their
cardinality) as elements of the incidence algebra. For instance the cardinality function, viewed as
an element of the incidence algebra, is simply the square of the function that takes constant value
one on all intervals. This constant function is called the zeta function, after
its connection with the Riemann zeta function.
The incidence algebra is a good setting for proving many inclusion-exclusion type principles, these
go under the name Möbius inversion, and are essentially due to the fact that the zeta function has
a multiplicative inverse in the incidence algebra, an inductively definable function called the
Möbius function that generalizes the Möbius function in number theory.

## References

- Aigner - Combinatorial Theory, Chapter IV
- Jacobson - Basic Algebra I, 8.6
- Rota - On the foundations of Combinatorial Theory
- Spiegel, O'Donnell - Incidence Algebras
- Kung, Rota, Yan - Combinatorics: The Rota Way, Chapter 3

## TODOs

Here are some additions to this file that could be made in the future:
- Generalize the construction of `mu` to invert any element of the incidence algebra `f` which has
  `f x x` a unit for all `x`.
- Give formulas for higher powers of zeta.
- A formula for the möbius function on a pi type similar to the one for products
- More examples / applications to different posets.
- Connection with Galois insertions
- Finsum version of Möbius inversion that holds even when an order doesn't have top/bot?
- Connect this theory to (infinite) matrices, giving maps of the incidence algebra to matrix rings
- Connect to the more advanced theory of arithmetic functions, and Dirichlet convolution.
-/

open Finset OrderDual
open scoped BigOperators

variable {𝕄 F 𝕜 𝕝 𝕞 α β : Type*}

/-- The `𝕜`-incidence algebra over `α`. -/
structure IncidenceAlgebra (𝕜 α : Type*) [Zero 𝕜] [LE α] where
  toFun : α → α → 𝕜
  eq_zero_of_not_le' ⦃a b : α⦄ : ¬a ≤ b → toFun a b = 0

namespace IncidenceAlgebra
section Zero
variable [Zero 𝕜] [LE α] {a b : α}

instance funLike : FunLike (IncidenceAlgebra 𝕜 α) α fun _ ↦ α → 𝕜 :=
  ⟨toFun, fun f g h ↦ by cases f; cases g; congr⟩

lemma apply_eq_zero_of_not_le (h : ¬a ≤ b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0 :=
  eq_zero_of_not_le' _ h

lemma le_of_ne_zero {f : IncidenceAlgebra 𝕜 α} : f a b ≠ 0 → a ≤ b :=
  not_imp_comm.1 fun h ↦ apply_eq_zero_of_not_le h _

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

-- this must come after the coe_toFun definitions
initialize_simps_projections IncidenceAlgebra (toFun → apply)

@[simp] lemma toFun_eq_coe (f : IncidenceAlgebra 𝕜 α) : f.toFun = f := rfl
@[simp, norm_cast] lemma coe_mk (f : α → α → 𝕜) (h) : (mk f h : α → α → 𝕜) = f := rfl

protected lemma congr_fun {f g : IncidenceAlgebra 𝕜 α} (h : f = g) (a b : α) : f a b = g a b :=
  congr_arg (fun f : IncidenceAlgebra 𝕜 α ↦ f a b) h

protected lemma congr_arg (f : IncidenceAlgebra 𝕜 α) {a₁ a₂ b₁ b₂ : α} (ha : a₁ = a₂)
    (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ :=
  congr_arg₂ f ha hb

@[simp]
lemma coe_inj {f g : IncidenceAlgebra 𝕜 α} : (f : α → α → 𝕜) = g ↔ f = g :=
  FunLike.coe_injective.eq_iff

@[ext]
lemma ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : ∀ a b, a ≤ b → f a b = g a b) : f = g := by
  refine' FunLike.coe_injective' (funext₂ fun a b ↦ _)
  by_cases hab : a ≤ b
  · exact h _ _ hab
  · rw [apply_eq_zero_of_not_le hab, apply_eq_zero_of_not_le hab]

lemma ext_iff {f g : IncidenceAlgebra 𝕜 α} : f = g ↔ ∀ a b, f a b = g a b :=
  ⟨IncidenceAlgebra.congr_fun, fun h ↦ ext fun _ _ _ ↦ h _ _⟩

@[simp] lemma mk_coe (f : IncidenceAlgebra 𝕜 α) (h) : mk f h = f := ext fun _ _ _ ↦ rfl

end Coes

/-! ### Additive and multiplicative structure -/

instance instZero : Zero (IncidenceAlgebra 𝕜 α) := ⟨⟨fun _ _ ↦ 0, fun _ _ _ ↦ rfl⟩⟩
instance instInhabited : Inhabited (IncidenceAlgebra 𝕜 α) := ⟨0⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : IncidenceAlgebra 𝕜 α) = 0 := rfl
lemma zero_apply (a b : α) : (0 : IncidenceAlgebra 𝕜 α) a b = 0 := rfl

end Zero

section Add
variable [AddZeroClass 𝕜] [LE α]

instance instAdd : Add (IncidenceAlgebra 𝕜 α) :=
  ⟨fun f g ↦ ⟨f + g, fun a b h ↦ by simp_rw [Pi.add_apply, apply_eq_zero_of_not_le h, zero_add]⟩⟩

@[simp, norm_cast] lemma coe_add (f g : IncidenceAlgebra 𝕜 α) : ⇑(f + g) = f + g := rfl
lemma add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g a b := rfl

end Add

section Smul

variable {M : Type*} [Zero 𝕜] [LE α] [SMulZeroClass M 𝕜]

instance instSmulZeroClassRight : SMulZeroClass M (IncidenceAlgebra 𝕜 α) where
  smul c f :=
    ⟨c • ⇑f, fun a b hab ↦ by simp_rw [Pi.smul_apply, apply_eq_zero_of_not_le hab, smul_zero]⟩
  smul_zero c := by ext; exact smul_zero _

@[simp, norm_cast] lemma coe_smul' (c : M) (f : IncidenceAlgebra 𝕜 α) : c • f = c • ⇑f := rfl

lemma smul_apply' (c : M) (f : IncidenceAlgebra 𝕜 α) (a b : α) : (c • f) a b = c • f a b := rfl

end Smul

instance instAddMonoid [AddMonoid 𝕜] [LE α] : AddMonoid (IncidenceAlgebra 𝕜 α) :=
  FunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ ↦ rfl

instance instAddCommMonoid [AddCommMonoid 𝕜] [LE α] : AddCommMonoid (IncidenceAlgebra 𝕜 α) :=
  FunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ ↦ rfl

section AddGroup
variable [AddGroup 𝕜] [LE α]

instance instNeg : Neg (IncidenceAlgebra 𝕜 α) :=
  ⟨fun f ↦ ⟨-f, fun a b h ↦ by simp_rw [Pi.neg_apply, apply_eq_zero_of_not_le h, neg_zero]⟩⟩

instance instSub : Sub (IncidenceAlgebra 𝕜 α) :=
  ⟨fun f g ↦ ⟨f - g, fun a b h ↦ by simp_rw [Pi.sub_apply, apply_eq_zero_of_not_le h, sub_zero]⟩⟩

@[simp, norm_cast] lemma coe_neg (f : IncidenceAlgebra 𝕜 α) : ⇑(-f) = -f := rfl
@[simp, norm_cast] lemma coe_sub (f g : IncidenceAlgebra 𝕜 α) : ⇑(f - g) = f - g := rfl
lemma neg_apply (f : IncidenceAlgebra 𝕜 α) (a b : α) : (-f) a b = -f a b := rfl
lemma sub_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g a b := rfl

instance instAddGroup : AddGroup (IncidenceAlgebra 𝕜 α) :=
  FunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end AddGroup

instance instAddCommGroup [AddCommGroup 𝕜] [LE α] : AddCommGroup (IncidenceAlgebra 𝕜 α) :=
  FunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

section One

variable [Preorder α] [DecidableEq α] [Zero 𝕜] [One 𝕜]

instance instOne : One (IncidenceAlgebra 𝕜 α) :=
  ⟨⟨fun a b ↦ if a = b then 1 else 0, fun _a _b h ↦ ite_eq_right_iff.2 fun H ↦ (h H.le).elim⟩⟩

@[simp]
lemma one_apply (a b : α) : (1 : IncidenceAlgebra 𝕜 α) a b = if a = b then 1 else 0 := rfl

end One

section Mul

variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Mul 𝕜]

instance : Mul (IncidenceAlgebra 𝕜 α) :=
  ⟨fun f g ↦
    ⟨fun a b ↦ ∑ x in Icc a b, f a x * g x b, fun a b h ↦ by dsimp; rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp]
lemma mul_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) :
    (f * g) a b = ∑ x in Icc a b, f a x * g x b := rfl

end Mul

instance instNonUnitalNonAssocSemiring [Preorder α] [LocallyFiniteOrder α]
    [NonUnitalNonAssocSemiring 𝕜] : NonUnitalNonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instAddCommMonoid
  mul := (· * ·)
  zero := 0
  zero_mul := fun f ↦ by ext; exact sum_eq_zero fun x _ ↦ MulZeroClass.zero_mul _
  mul_zero := fun f ↦ by ext; exact sum_eq_zero fun x _ ↦ MulZeroClass.mul_zero _
  left_distrib := fun f g h ↦ by
    ext; exact Eq.trans (sum_congr rfl fun x _ ↦ left_distrib _ _ _) sum_add_distrib
  right_distrib := fun f g h ↦ by
    ext; exact Eq.trans (sum_congr rfl fun x _ ↦ right_distrib _ _ _) sum_add_distrib

instance instNonAssocSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]
    [NonAssocSemiring 𝕜] : NonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonUnitalNonAssocSemiring
  mul := (· * ·)
  zero := 0
  one := 1
  one_mul := fun f ↦ by
    ext a b
    simp_rw [mul_apply, one_apply, sum_boole_mul]
    exact ite_eq_left_iff.2 (not_imp_comm.1 fun h ↦ left_mem_Icc.2 <| le_of_ne_zero <| Ne.symm h)
  mul_one := fun f ↦ by
    ext a b
    simp_rw [mul_apply, one_apply, eq_comm, sum_mul_boole]
    convert
      (ite_eq_left_iff.2 <|
          not_imp_comm.1 fun h ↦ right_mem_Icc.2 <| le_of_ne_zero <| Ne.symm h).symm

instance instSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] :
    Semiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonAssocSemiring
  mul := (· * ·)
  mul_assoc := fun f g h ↦ by
    ext a b
    simp only [mul_apply, sum_mul, mul_sum]
    rw [sum_sigma', sum_sigma']
    apply sum_bij fun x _ ↦ Sigma.mk x.snd x.fst
    · rintro c hc
      simp only [mem_sigma, mem_Icc] at hc
      simp only [mem_sigma, mem_Icc]
      exact ⟨⟨hc.2.1, hc.2.2.trans hc.1.2⟩, hc.2.2, hc.1.2⟩
    · rintro c _
      simp only [mul_assoc]
    · rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ hc hd ⟨⟩
      rfl
    · rintro c hc
      simp only [exists_prop, Sigma.exists, mem_sigma, heq_iff_eq, Sigma.mk.inj_iff, mem_Icc] at *
      exact ⟨c.2, c.1, ⟨⟨hc.1.1.trans hc.2.1, hc.2.2⟩, hc.1.1, hc.2.1⟩, c.eta.symm⟩
  one := 1
  zero := 0

instance [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Ring 𝕜] :
    Ring (IncidenceAlgebra 𝕜 α) where
  __ := instSemiring
  __ := instAddGroup

/-! ### Scalar multiplication between incidence algebras -/

section Smul

variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [AddCommMonoid 𝕝] [SMul 𝕜 𝕝]

instance instSMul : SMul (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) :=
  ⟨fun f g ↦
    ⟨fun a b ↦ ∑ x in Icc a b, f a x • g x b, fun a b h ↦ by dsimp; rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp]
lemma smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α) :
    (f • g) a b = ∑ x in Icc a b, f a x • g x b :=
  rfl

end Smul

instance instIsScalarTower [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Monoid 𝕜]
    [Semiring 𝕝] [AddCommMonoid 𝕞] [SMul 𝕜 𝕝] [Module 𝕝 𝕞] [DistribMulAction 𝕜 𝕞]
    [IsScalarTower 𝕜 𝕝 𝕞] :
    IsScalarTower (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) (IncidenceAlgebra 𝕞 α) :=
  ⟨fun f g h ↦ by
    ext a b
    simp only [smul_apply, sum_smul, smul_sum]
    rw [sum_sigma', sum_sigma']
    apply sum_bij fun x _ ↦ Sigma.mk x.snd x.fst
    · rintro c hc
      simp only [mem_sigma, mem_Icc] at hc
      simp only [mem_sigma, mem_Icc]
      exact ⟨⟨hc.2.1, hc.2.2.trans hc.1.2⟩, hc.2.2, hc.1.2⟩
    · rintro c _
      simp only [smul_assoc]
    · rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ hc hd ⟨⟩
      rfl
    · rintro c hc
      simp only [exists_prop, Sigma.exists, mem_sigma, heq_iff_eq, Sigma.mk.inj_iff, mem_Icc] at *
      exact ⟨c.2, c.1, ⟨⟨hc.1.1.trans hc.2.1, hc.2.2⟩, hc.1.1, hc.2.1⟩, c.eta.symm⟩⟩

instance [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] [Semiring 𝕝]
    [Module 𝕜 𝕝] : Module (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) where
  smul := (· • ·)
  one_smul f := by ext a b hab; simp [ite_smul, hab]
  mul_smul f g h := by convert smul_assoc _ _ _; ext a b; rfl; infer_instance
  smul_add f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ ↦ smul_add _ _ _) sum_add_distrib
  add_smul f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ ↦ add_smul _ _ _) sum_add_distrib
  zero_smul f := by ext; exact sum_eq_zero fun x _ ↦ zero_smul _ _
  smul_zero f := by ext; exact sum_eq_zero fun x _ ↦ smul_zero _

instance smulWithZeroRight [Zero 𝕜] [Zero 𝕝] [SMulWithZero 𝕜 𝕝] [LE α] :
    SMulWithZero 𝕜 (IncidenceAlgebra 𝕝 α) :=
  Function.Injective.smulWithZero ⟨((⇑) : IncidenceAlgebra 𝕝 α → α → α → 𝕝), coe_zero⟩
    FunLike.coe_injective coe_smul'

instance moduleRight [Preorder α] [Semiring 𝕜] [AddCommMonoid 𝕝] [Module 𝕜 𝕝] :
    Module 𝕜 (IncidenceAlgebra 𝕝 α) :=
  Function.Injective.module _ ⟨⟨((⇑) : IncidenceAlgebra 𝕝 α → α → α → 𝕝), coe_zero⟩, coe_add⟩
    FunLike.coe_injective coe_smul'

#exit

instance algebraRight [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [CommSemiring 𝕜]
    [CommSemiring 𝕝] [Algebra 𝕜 𝕝] : Algebra 𝕜 (IncidenceAlgebra 𝕝 α) where
  toFun c := algebraMap 𝕜 𝕝 c • (1 : IncidenceAlgebra 𝕝 α)
  map_one' := by
    ext; simp only [mul_boole, one_apply, Algebra.id.smul_eq_mul, smul_apply', map_one]
  map_mul' c d := by
    ext a b
    obtain rfl | h := eq_or_ne a b
    · simp only [smul_boole, one_apply, Algebra.id.smul_eq_mul, mul_apply, Algebra.mul_smul_comm,
        boole_smul, smul_apply', ← ite_and, algebraMap_smul, map_mul, Algebra.smul_mul_assoc,
        if_pos rfl, eq_comm, and_self_iff, Icc_self]
      simp only [mul_one, if_true, Algebra.mul_smul_comm, smul_boole, MulZeroClass.zero_mul,
        ite_mul, sum_ite_eq, Algebra.smul_mul_assoc, mem_singleton]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp only [mul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, if_pos rfl]
    · simp only [true_and_iff, ite_self, le_rfl, one_apply, mul_one, Algebra.id.smul_eq_mul,
        mul_apply, Algebra.mul_smul_comm, smul_boole, MulZeroClass.zero_mul, smul_apply',
        algebraMap_smul, ← ite_and, ite_mul, mul_ite, map_mul, mem_Icc, sum_ite_eq,
        MulZeroClass.mul_zero, smul_zero, Algebra.smul_mul_assoc, if_pos rfl, if_neg h]
      refine' (sum_eq_zero fun x _ ↦ _).symm
      exact if_neg fun hx ↦ h <| hx.2.trans hx.1
  map_zero' := by dsimp; rw [map_zero, zero_smul]
  map_add' c d := by dsimp; rw [map_add, add_smul]
  commutes' c f := by classical ext a b hab; simp [if_pos hab]
  smul_def' c f := by classical ext a b hab; simp [if_pos hab]

/-! ### The Lambda function -/

section Lambda

variable (𝕜) [Zero 𝕜] [One 𝕜] [Preorder α] [@DecidableRel α (· ⩿ ·)]

/-- The lambda function of the incidence algebra is the function that assigns `1` to every nonempty
interval of cardinality one or two. -/
def lambda : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b ↦ if a ⩿ b then 1 else 0, fun _a _b h ↦ if_neg fun hh ↦ h hh.le⟩

variable {𝕜}

-- TODO: Can't this be autogenerated?
@[simp] lemma lambda_apply (a b : α) : lambda 𝕜 a b = if a ⩿ b then 1 else 0 := rfl

end Lambda

/-! ### The Zeta and Möbius functions -/

section Zeta

variable (𝕜) [Zero 𝕜] [One 𝕜] [LE α] [@DecidableRel α (· ≤ ·)] {a b : α}

/-- The zeta function of the incidence algebra is the function that assigns 1 to every nonempty
interval, convolution with this function sums functions over intervals. -/
def zeta : IncidenceAlgebra 𝕜 α := ⟨fun a b ↦ if a ≤ b then 1 else 0, fun _a _b h ↦ if_neg h⟩

variable {𝕜}

@[simp] lemma zeta_apply (a b : α) : zeta 𝕜 a b = if a ≤ b then 1 else 0 := rfl

lemma zeta_of_le (h : a ≤ b) : zeta 𝕜 a b = 1 := if_pos h

end Zeta

lemma zeta_mul_zeta [Semiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [@DecidableRel α (· ≤ ·)]
    (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
  rw [mul_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine' sum_congr rfl fun x hx ↦ _
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul]

lemma zeta_mul_kappa [Semiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [@DecidableRel α (· ≤ ·)]
    (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
  rw [mul_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine' sum_congr rfl fun x hx ↦ _
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul]

section Mu

variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

/-- The Möbius function of the incidence algebra as a bare function defined recursively. -/
def muAux (a : α) : α → 𝕜
  | b =>
    if h : a = b then 1
    else
      -∑ x in (Ico a b).attach,
          let h := mem_Ico.1 x.2
          have : (Icc a x).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2)
          muAux x
termination_by' ⟨_, measure_wf fun b ↦ (Icc a b).card⟩

lemma muAux_apply (a b : α) :
    muAux 𝕜 a b = if a = b then 1 else -∑ x in (Ico a b).attach, muAux 𝕜 a x := by
  convert IsWellFounded.wf.fix_eq _ _; rfl

/-- The Möbius function which inverts `zeta` as an element of the incidence algebra. -/
def mu : IncidenceAlgebra 𝕜 α :=
  ⟨muAux 𝕜, fun a b ↦
    not_imp_comm.1 fun h ↦ by
      rw [muAux_apply] at h
      split_ifs at h  with hab
      · exact hab.le
      · rw [neg_eq_zero] at h
        obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (nonempty_Ico.1 ⟨x, hx⟩).le⟩

variable {𝕜}

lemma mu_apply (a b : α) : mu 𝕜 a b = if a = b then 1 else -∑ x in Ico a b, mu 𝕜 a x := by
  rw [mu, coe_mk, muAux_apply, sum_attach]

lemma mu_apply_of_eq {a b : α} (h : a = b) : mu 𝕜 a b = 1 := by rw [mu_apply, if_pos h]

@[simp] lemma mu_apply_self (a : α) : mu 𝕜 a a = 1 := mu_apply_of_eq rfl

lemma mu_apply_of_ne {a b : α} (h : a ≠ b) : mu 𝕜 a b = -∑ x in Ico a b, mu 𝕜 a x := by
  rw [mu_apply, if_neg h]

end Mu

section MuSpec
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

-- we need partial order for this
lemma mu_spec_of_ne_right {a b : α} (h : a ≠ b) : ∑ x in Icc a b, mu 𝕜 a x = 0 := by
  have : mu 𝕜 a b = _ := mu_apply_of_ne h
  by_cases hab : a ≤ b
  · rw [← add_sum_Ico hab, this, neg_add_self]
  · have : ∀ x ∈ Icc a b, ¬a ≤ x := by intro x hx hn; apply hab; rw [mem_Icc] at hx ;
      exact le_trans hn hx.2
    conv in mu _ _ _ ↦ rw [apply_eq_zero_of_not_le (this x H)]
    exact sum_const_zero

end MuSpec

section Mu'

variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

-- this is the reversed definition of mu, which is equal to mu but easiest to prove equal
-- by showing that zeta * mu = 1 and mu' * zeta = 1
-- therefore mu' should be an implementation detail and not used
private def mu'Aux (b : α) : α → 𝕜
  | a =>
    if h : a = b then 1
    else
      -∑ x in (Ioc a b).attach,
          let h := mem_Ioc.1 x.2
          have : (Icc (↑x) b).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)
          mu'Aux x
termination_by' ⟨_, measure_wf fun a ↦ (Icc a b).card⟩

private lemma mu'Aux_apply (a b : α) :
    mu'Aux 𝕜 b a = if a = b then 1 else -∑ x in (Ioc a b).attach, mu'Aux 𝕜 b x := by
  convert IsWellFounded.wf.fix_eq _ _; rfl

private def mu' : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b ↦ mu'Aux 𝕜 b a, fun a b ↦
    not_imp_comm.1 fun h ↦ by
      rw [mu'Aux_apply] at h
      split_ifs at h  with hab hab
      · exact hab.le
      · rw [neg_eq_zero] at h
        obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (nonempty_Ioc.1 ⟨x, hx⟩).le⟩

variable {𝕜}

lemma mu'_apply (a b : α) : mu' 𝕜 a b = if a = b then 1 else -∑ x in Ioc a b, mu' 𝕜 x b := by
  rw [mu', coe_mk, mu'Aux_apply, sum_attach]

lemma mu'_apply_of_ne {a b : α} (h : a ≠ b) : mu' 𝕜 a b = -∑ x in Ioc a b, mu' 𝕜 x b := by
  rw [mu'_apply, if_neg h]

lemma mu'_apply_of_eq {a b : α} (h : a = b) : mu' 𝕜 a b = 1 := by rw [mu'_apply, if_pos h]

@[simp]
lemma mu'_apply_self (a : α) : mu' 𝕜 a a = 1 :=
  mu'_apply_of_eq rfl

end Mu'

section Mu'Spec
-- we need partial order for this
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

lemma mu'_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ x in Icc a b, (mu' 𝕜) x b = 0 := by
  have : mu' 𝕜 a b = _ := mu'_apply_of_ne h by_cases hab : a ≤ b
  · rw [← add_sum_Ioc hab, this, neg_add_self]
  · have : ∀ x ∈ Icc a b, ¬x ≤ b := by intro x hx hn; apply hab; rw [mem_Icc] at hx ;
      exact le_trans hx.1 hn
    conv in mu' _ _ _ ↦ rw [apply_eq_zero_of_not_le (this x H)]
    exact sum_const_zero

end Mu'Spec

section MuZeta

variable (𝕜 α) [AddCommGroup 𝕜] [MulOneClass 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
  [DecidableEq α] [@DecidableRel α (· ≤ ·)]

lemma mu_mul_zeta : (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  rw [mul_apply, one_apply]
  split_ifs with he
  · simp [he]
  · simp only [mul_one, zeta_apply, mul_ite]
    conv in ite _ _ _ ↦ rw [if_pos (mem_Icc.mp H).2]
    rw [mu_spec_of_ne_right he]

lemma zeta_mul_mu' : (zeta 𝕜 * mu' 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  rw [mul_apply, one_apply]
  split_ifs with he
  · simp [he]
  · simp only [zeta_apply, one_mul, ite_mul]
    conv in ite _ _ _ ↦ rw [if_pos (mem_Icc.mp H).1]
    rw [mu'_spec_of_ne_left he]

end MuZeta

section MuEqMu'

variable [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

lemma mu_eq_mu' : (mu 𝕜 : IncidenceAlgebra 𝕜 α) = mu' 𝕜 :=
  left_inv_eq_right_inv (mu_mul_zeta _ _) (zeta_mul_mu' _ _)

lemma mu_apply_of_ne' {a b : α} (h : a ≠ b) : mu 𝕜 a b = -∑ x in Ioc a b, mu 𝕜 x b := by
  rw [mu_eq_mu']; exact mu'_apply_of_ne h

lemma zeta_mul_mu [@DecidableRel α (· ≤ ·)] : (zeta 𝕜 * mu 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  rw [mu_eq_mu']; exact zeta_mul_mu' _ _

lemma mu_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ x in Icc a b, mu 𝕜 x b = 0 := by
  rw [mu_eq_mu', mu'_spec_of_ne_left h]

end MuEqMu'

section OrderDual

variable (𝕜) [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

@[simp]
lemma mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDual b) = mu 𝕜 b a := by
  letI : @DecidableRel α (· ≤ ·) := Classical.decRel _
  let mud : IncidenceAlgebra 𝕜 αᵒᵈ :=
    { toFun := fun a b ↦ mu 𝕜 (of_dual b) (of_dual a)
      eq_zero_of_not_le' := fun a b hab ↦ apply_eq_zero_of_not_le hab _ }
  suffices mu 𝕜 = mud by rw [this]; rfl
  suffices mud * zeta 𝕜 = 1 by
    rw [← mu_mul_zeta] at this
    apply_fun (· * mu 𝕜) at this
    symm
    simpa [mul_assoc, zeta_mul_mu] using this
  clear a b
  ext a b
  simp only [mul_boole, one_apply, mul_apply, coe_mk, zeta_apply]
  obtain rfl | h := eq_or_ne a b
  · simp
  · rw [if_neg h]
    conv in ite _ _ _ ↦ rw [if_pos (mem_Icc.mp H).2]
    change ∑ x in Icc (of_dual b) (of_dual a), mu 𝕜 x a = 0
    exact mu_spec_of_ne_left h.symm

@[simp]
lemma mu_ofDual (a b : αᵒᵈ) : mu 𝕜 (ofDual a) (ofDual b) = mu 𝕜 b a :=
  (mu_toDual _ _ _).symm

end OrderDual

section InversionTop

variable {α} [Ring 𝕜] [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α] [DecidableEq α] {a b : α}

/-- A general form of Möbius inversion. Based on lemma 2.1.2 of Incidence Algebras by Spiegel and
O'Donnell. -/
lemma moebius_inversion_top (f g : α → 𝕜) (h : ∀ x, g x = ∑ y in Ici x, f y) (x : α) :
    f x = ∑ y in Ici x, mu 𝕜 x y * g y := by
  letI : @DecidableRel α (· ≤ ·) := Classical.decRel _ <;> symm <;>
    calc
      ∑ y in Ici x, mu 𝕜 x y * g y = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, f z := by simp_rw [h]
      _ = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, zeta 𝕜 y z * f z := by
        simp_rw [zeta_apply]
        conv in ite _ _ _ ↦ rw [if_pos (mem_Ici.mp H)]
        simp
      _ = ∑ y in Ici x, ∑ z in Ici y, mu 𝕜 x y * zeta 𝕜 y z * f z := by simp [mul_sum]
      _ = ∑ z in Ici x, ∑ y in Icc x z, mu 𝕜 x y * zeta 𝕜 y z * f z := by
        erw [sum_sigma' (Ici x) fun y ↦ Ici y]
        erw [sum_sigma' (Ici x) fun z ↦ Icc x z]
        simp only [mul_boole, MulZeroClass.zero_mul, ite_mul, zeta_apply]
        refine' sum_bij (fun X hX ↦ ⟨X.snd, X.fst⟩) _ _ _ _
        · intro X hX
          simp only [mem_Ici, mem_sigma, mem_Icc] at *
          exact ⟨hX.1.trans hX.2, hX⟩
        · intro X hX
          simp only at *
        · intro X Y ha hb h
          simp [Sigma.ext_iff] at *
          rwa [and_comm']
        · intro X hX
          use⟨X.snd, X.fst⟩
          simp only [and_true_iff, mem_Ici, eq_self_iff_true, Sigma.eta, mem_sigma, mem_Icc] at *
          exact hX.2
      _ = ∑ z in Ici x, (mu 𝕜 * zeta 𝕜) x z * f z := by
        conv in (mu _ * zeta _) _ _ ↦ rw [mul_apply]
        simp_rw [sum_mul]
      _ = ∑ y in Ici x, ∑ z in Ici y, (1 : IncidenceAlgebra 𝕜 α) x z * f z := by
        simp [mu_mul_zeta 𝕜, ← add_sum_Ioi]
        conv in ite _ _ _ ↦ rw [if_neg (ne_of_lt <| mem_Ioi.mp H)]
        conv in ite _ _ _ ↦ rw [if_neg (not_lt_of_le <| (mem_Ioi.mp H).le)]
        simp
      _ = f x := by
        simp [one_apply, ← add_sum_Ioi]
        conv in ite _ _ _ ↦ rw [if_neg (ne_of_lt <| mem_Ioi.mp H)]
        conv in ite _ _ _ ↦ rw [if_neg (not_lt_of_le <| (mem_Ioi.mp H).le)]
        simp

end InversionTop

section InversionBot

variable [Ring 𝕜] [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α]

/-- A general form of Möbius inversion. Based on lemma 2.1.3 of Incidence Algebras by Spiegel and
O'Donnell. -/
lemma moebius_inversion_bot (f g : α → 𝕜) (h : ∀ x, g x = ∑ y in Iic x, f y) (x : α) :
    f x = ∑ y in Iic x, mu 𝕜 y x * g y := by
  convert @moebius_inversion_top 𝕜 αᵒᵈ _ _ _ _ _ f g h x
  ext y
  erw [mu_to_dual]

end InversionBot

section Prod

section Preorder

section Ring

variable (𝕜) [Ring 𝕜] [Preorder α] [Preorder β]

section DecidableLe

variable [DecidableRel ((· ≤ ·) : α → α → Prop)] [DecidableRel ((· ≤ ·) : β → β → Prop)]

lemma zeta_prod_apply (a b : α × β) : zeta 𝕜 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b.2 := by
  simp [ite_and, Prod.le_def]

lemma zeta_prod_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    zeta 𝕜 (a₁, b₁) (a₂, b₂) = zeta 𝕜 a₁ a₂ * zeta 𝕜 b₁ b₂ :=
  zeta_prod_apply _ _ _

end DecidableLe

variable {𝕜} (f f₁ f₂ : IncidenceAlgebra 𝕜 α) (g g₁ g₂ : IncidenceAlgebra 𝕜 β)

/-- The cartesian product of two incidence algebras. -/
protected def prod : IncidenceAlgebra 𝕜 (α × β) where
  toFun x y := f x.1 y.1 * g x.2 y.2
  eq_zero_of_not_le' x y hxy := by
    rw [Prod.le_def, not_and_or] at hxy
    cases hxy <;> simp [apply_eq_zero_of_not_le hxy]

lemma prod_mk (a₁ a₂ : α) (b₁ b₂ : β) : f.prod g (a₁, b₁) (a₂, b₂) = f a₁ a₂ * g b₁ b₂ := rfl
@[simp] lemma prod_apply (x y : α × β) : f.prod g x y = f x.1 y.1 * g x.2 y.2 := rfl

/-- This is a version of `incidence_algebra.prod_mul_prod` that works over non-commutative rings. -/
lemma prod_mul_prod' [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    (h : ∀ a₁ a₂ a₃ b₁ b₂ b₃,
        f₁ a₁ a₂ * g₁ b₁ b₂ * (f₂ a₂ a₃ * g₂ b₂ b₃) = f₁ a₁ a₂ * f₂ a₂ a₃ * (g₁ b₁ b₂ * g₂ b₂ b₃)) :
    f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) := by ext x y hxy;
  simp [← prod_Icc, sum_mul_sum, h]

@[simp]
lemma one_prod_one [DecidableEq α] [DecidableEq β] :
    (1 : IncidenceAlgebra 𝕜 α).prod (1 : IncidenceAlgebra 𝕜 β) = 1 := by ext x y hxy;
  simp [Prod.ext_iff, ite_and]

@[simp]
lemma zeta_prod_zeta [@DecidableRel α (· ≤ ·)] [@DecidableRel β (· ≤ ·)] :
    (zeta 𝕜).prod (zeta 𝕜) = (zeta 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by ext x y hxy;
  simp [hxy, hxy.1, hxy.2]

end Ring

section CommRing

variable [CommRing 𝕜] [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  (f₁ f₂ : IncidenceAlgebra 𝕜 α) (g₁ g₂ : IncidenceAlgebra 𝕜 β)

@[simp]
lemma prod_mul_prod : f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) :=
  prod_mul_prod' _ _ _ _ fun _ _ _ _ _ _ ↦ mul_mul_mul_comm _ _ _ _

end CommRing
end Preorder

section PartialOrder

variable (𝕜) [Ring 𝕜] [PartialOrder α] [PartialOrder β] [LocallyFiniteOrder α]
  [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β] [DecidableRel ((· ≤ ·) : α → α → Prop)]
  [DecidableRel ((· ≤ ·) : β → β → Prop)]

/-- The Möbius function on a product order. Based on lemma 2.1.13 of Incidence Algebras by Spiegel and O'Donnell. -/
@[simp]
lemma mu_prod_mu : (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  refine' left_inv_eq_right_inv _ zeta_mul_mu
  rw [← zeta_prod_zeta, prod_mul_prod', mu_mul_zeta, mu_mul_zeta, one_prod_one]
  refine' fun _ _ _ _ _ _ ↦ Commute.mul_mul_mul_comm _ _ _
  dsimp
  split_ifs <;> simp

end PartialOrder
end Prod

section Euler

variable [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [BoundedOrder α] [LocallyFiniteOrder α]
  [DecidableEq α]

/-- The Euler characteristic of a finite bounded order. -/
def eulerChar : 𝕜 := mu 𝕜 (⊥ : α) ⊤

end Euler
end IncidenceAlgebra
