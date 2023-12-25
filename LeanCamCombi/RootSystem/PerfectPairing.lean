import Mathlib.LinearAlgebra.Dual
import LeanCamCombi.RootSystem.LinearAlgebraAux

noncomputable section

open Set Function

namespace Module

variable (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M]

@[simp]
theorem flip_dual_eval : (Dual.eval R M).flip = LinearMap.id := by
  ext
  simp only [LinearMap.flip_apply, LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply,
    dual.eval_apply, LinearMap.id_coe, id.def]

@[simp]
theorem LinearMap.dualMap_comp_dual_eval (N : Type _) [AddCommMonoid N] [Module R N]
    (e : M →ₗ[R] Dual R N) :
    (e.dualMap : Dual R (Dual R N) →ₗ[R] Dual R M) ∘ₗ Dual.eval R N = e.flip :=
  rfl

section IsReflexive

#print Module.IsReflexive /-
/- ./././Mathport/Syntax/Translate/Command.lean:404:30: infer kinds are unsupported in Lean 4: #[`bijective_dual_eval] [] -/
/-- A reflexive `R`-module `M` is one for which the natural map: `M → dual R (dual R M)` is a
bijection. -/
class IsReflexive : Prop where
  bijective_dual_eval : Bijective <| Dual.eval R M
-/

def evalEquiv' [IsReflexive R M] : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective _ <| IsReflexive.bijective_dual_eval R M

@[simp]
theorem apply_evalEquiv'_symm_apply [IsReflexive R M] (f : Module.Dual R M)
    (g : Module.Dual R <| Module.Dual R M) : f ((evalEquiv' R M).symm g) = g f := by
  set n := (eval_equiv' R M).symm g
  have hn : g = eval_equiv' R M n := (LinearEquiv.apply_symm_apply _ _).symm
  rw [hn]
  rfl

theorem symm_dualMap_evalEquiv' [IsReflexive R M] :
    ↑(evalEquiv' R M).dualMap.symm = Dual.eval R (Dual R M) := by
  ext f g
  simp only [LinearEquiv.dualMap_symm, LinearEquiv.coe_coe, LinearEquiv.dualMap_apply,
    apply_eval_equiv'_symm_apply, dual.eval_apply]

instance [IsReflexive R M] : IsReflexive R (Dual R M) :=
  ⟨by rw [← symm_dual_map_eval_equiv']; exact (eval_equiv' R M).dualMap.symm.Bijective⟩

instance isReflexive_of_finite_free [Module.Finite R M] [Module.Free R M] [Nontrivial R] :
    IsReflexive R M :=
  ⟨⟨LinearMap.ker_eq_bot.mp (Free.chooseBasis R M).eval_ker,
      LinearMap.range_eq_top.mp (Free.chooseBasis R M).eval_range⟩⟩

end IsReflexive

section PerfectPairing

variable (N P : Type _) [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A perfect pairing between two modules `M` and `N` is a bilinear map `M × N → R`
such that the induces maps `M → N*` and `N → M*` are both bijective.

To see that `bijective_flip_to_lin` is necessary, consider the pairing between `dual R M` and
`M` given by the identity map. This satisfies `bijective_flip_to_lin` only if `M` is reflexive. -/
@[protect_proj]
structure PerfectPairing where
  toLin : M →ₗ[R] Dual R N
  bijective_toLin : Bijective to_lin
  bijective_flip_toLin : Bijective to_lin.flip

namespace PerfectPairing

variable {R M N P} (p : PerfectPairing R M N) (q : PerfectPairing R N P)

protected def symm : PerfectPairing R N M
    where
  toLin := p.toLin.flip
  bijective_toLin := p.bijective_flip_toLin
  bijective_flip_toLin := by simp only [p.bijective_to_lin, LinearMap.flip_flip]

@[simp]
theorem symm_toLin_eq_flip_toLin : p.symm.toLin = p.toLin.flip :=
  rfl

protected def toEquiv : M ≃ₗ[R] Dual R N :=
  LinearEquiv.ofBijective p.toLin p.bijective_toLin

protected def toEquiv' : N ≃ₗ[R] Dual R M :=
  p.symm.toEquiv

theorem dualMap_flip_toEquiv_trans_toEquiv_symm :
    (p.toEquiv.trans q.toEquiv.symm.dualMap : M →ₗ[R] Dual R (Dual R P)).flip =
      (q.toEquiv.symm.trans p.toEquiv' : Dual R P →ₗ[R] Dual R M) := by
  ext f m
  simp only [perfect_pairing.to_equiv, perfect_pairing.to_equiv', LinearMap.flip_apply,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    LinearEquiv.dualMap_apply, symm_to_lin_eq_flip_to_lin]

protected def trans : PerfectPairing R M (Dual R P)
    where
  toLin := (p.toEquiv.trans q.toEquiv.symm.dualMap : M →ₗ[R] Dual R (Dual R P))
  bijective_toLin := LinearEquiv.bijective _
  bijective_flip_toLin := by rw [dual_map_flip_to_equiv_trans_to_equiv_symm];
    exact LinearEquiv.bijective _

theorem trans_symm_toLin : (p.trans p.symm).toLin = Dual.eval R M := by
  -- TODO Fix this proof (mostly by adding missing API for `symm` and `trans`)
  ext m f
  simp only [perfect_pairing.to_equiv, perfect_pairing.symm, perfect_pairing.trans,
    LinearEquiv.coe_coe, dual.eval_apply, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    LinearEquiv.ofBijective_apply]
  rw [← p.to_lin.flip_apply]
  let e := LinearEquiv.ofBijective p.to_lin.flip p.bijective_flip_to_lin
  erw [e.apply_symm_apply f]

protected theorem isReflexive (p : PerfectPairing R M N) : IsReflexive R M :=
  ⟨by rw [← p.trans_symm_to_lin]; exact perfect_pairing.bijective_to_lin _⟩

protected theorem is_reflexive' (p : PerfectPairing R M N) : IsReflexive R N :=
  ⟨by rw [← p.symm.trans_symm_to_lin]; exact perfect_pairing.bijective_to_lin _⟩

/-- If `N` is reflexive, then a linear equivalence to its dual induces a perfect pairing. -/
def ofIsReflexive' [IsReflexive R N] (B : M ≃ₗ[R] Dual R N) : PerfectPairing R M N
    where
  toLin := (B : M →ₗ[R] Dual R N)
  bijective_toLin := B.Bijective
  bijective_flip_toLin := B.dualMap.Bijective.comp <| IsReflexive.bijective_dual_eval R N

variable (R M)

/-- A reflexive module has a natural perfect pairing with its dual. -/
def ofIsReflexive [IsReflexive R M] : PerfectPairing R M (Dual R M) :=
  ofIsReflexive' <| evalEquiv' R M

end PerfectPairing

end PerfectPairing

namespace IsRootDatum

-- variables [is_reflexive R M] (p : perfect_pairing R M (dual R M)) (X : Type*) [add_comm_group X] [module ℤ X]
-- [is_reflexive ℤ X] [n : perfect_pairing ℤ X (dual ℤ X)]
variable (X Y : Type _) [AddCommGroup X] [AddCommGroup Y] (p : PerfectPairing ℤ X Y)
  [Module.Free ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ X] [Module.Finite ℤ Y] (Φ : Set X)
  (Ψ : Set Y)

-- example : module ℤ X := add_comm_group.int_module X
-- Would be a bit less useful because it would force the coroots to live in the dual
-- Perfect pairing gives isomorphism to dual, but not equality. We don't always want to force the
-- 2nd space to be the dual because it might just be another additive group (ℤ-module).
example : PerfectPairing ℤ X (Dual ℤ X) :=
  PerfectPairing.ofIsReflexive ℤ X

structure IsRootPairing (e : Φ ≃ Ψ) : Prop where
  perfectPairing_eq_two : ∀ α : Φ, p.toEquiv' (e α : Y) α = 2
  foo : ∀ α : Φ, Module.toPreSymmetry (α : X) (p.toEquiv' (e α : Y)) '' Φ ⊆ Φ
  foo' : ∀ α : Ψ, Module.toPreSymmetry (α : Y) (p.toEquiv (e.symm α : X)) '' Ψ ⊆ Ψ

class IsRootDatum : Prop where
  Finite : Φ.Finite
  exists_equiv : ∃ e : Φ ≃ Ψ, IsRootPairing X Y p Φ Ψ e

end IsRootDatum

end Module
