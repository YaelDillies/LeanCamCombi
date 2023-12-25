import GroupTheory.OrderOfElement
import LinearAlgebra.Contraction
import LinearAlgebra.BilinearForm
import LinearAlgebra.QuadraticForm.Basic

noncomputable section

open scoped TensorProduct BigOperators Classical Pointwise

open Set Function

#print Module.apply_evalEquiv_symm_apply /-
@[simp]
theorem Module.apply_evalEquiv_symm_apply {k V : Type _} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : Module.Dual k V) (v : Module.Dual k <| Module.Dual k V) :
    f ((Module.evalEquiv k V).symm v) = v f := by
  set w := (Module.evalEquiv k V).symm v
  have hw : v = Module.evalEquiv k V w := (LinearEquiv.apply_symm_apply _ _).symm
  rw [hw]
  rfl
-/

@[simp]
theorem Module.coe_end_one {k V : Type _} [Semiring k] [AddCommMonoid V] [Module k V] :
    ⇑(1 : (Module.End k V)ˣ) = id :=
  rfl

#print LinearEquiv.coe_one /-
@[simp]
theorem LinearEquiv.coe_one {k V : Type _} [Semiring k] [AddCommMonoid V] [Module k V] :
    ⇑(1 : V ≃ₗ[k] V) = id :=
  rfl
-/

@[simp]
theorem LinearEquiv.coe_hMul {k V : Type _} [Semiring k] [AddCommMonoid V] [Module k V]
    {e₁ e₂ : V ≃ₗ[k] V} : (↑(e₁ * e₂) : V →ₗ[k] V) = (e₁ : V →ₗ[k] V) * (e₂ : V →ₗ[k] V) := by ext;
  simpa

attribute [protected] Module.Finite

namespace Module

variable {k V : Type _} [CommRing k] [AddCommGroup V] [Module k V]

/-- Given a vector `x` and a linear form `f`, this is the map `y ↦ y - (f y) • x`, bundled as a
linear endomorphism.

When `f x = 2`, it is involutive and sends `x ↦ - x`. See also `module.to_symmetry`. -/
def toPreSymmetry (x : V) (f : Dual k V) : End k V :=
  LinearMap.id - dualTensorHom k V V (f ⊗ₜ x)

@[simp]
theorem toPreSymmetry_apply (x y : V) (f : Dual k V) : toPreSymmetry x f y = y - f y • x := by
  simp [to_pre_symmetry]

theorem toPreSymmetry_apply_self {x : V} {f : Dual k V} (h : f x = 2) : toPreSymmetry x f x = -x :=
  by rw [to_pre_symmetry_apply, h, ← one_smul k x, smul_smul, ← sub_smul]; norm_num

theorem toPreSymmetry_sq {x : V} {f : Dual k V} (h : f x = 2) :
    toPreSymmetry x f ^ 2 = LinearMap.id := by
  ext β
  rw [LinearMap.pow_apply, iterate_succ, iterate_one, comp_app]
  nth_rw 2 [to_pre_symmetry_apply]
  rw [map_sub, map_smul, to_pre_symmetry_apply_self h, to_pre_symmetry_apply, smul_neg,
    sub_neg_eq_add, sub_add_cancel, LinearMap.id_apply]

/-- Given a vector `x` and a linear form `f` such that `f x = 2`, this is the map
`y ↦ y - (f y) • x`, bundled as a linear automorphism. -/
def toSymmetry {x : V} {f : Dual k V} (h : f x = 2) : V ≃ₗ[k] V :=
  { toPreSymmetry x f with
    invFun := toPreSymmetry x f
    left_inv := fun v => by
      simp only [LinearMap.toFun_eq_coe, ← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, ← sq,
        to_pre_symmetry_sq h, LinearMap.id_apply]
    right_inv := fun v => by
      simp only [LinearMap.toFun_eq_coe, ← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, ← sq,
        to_pre_symmetry_sq h, LinearMap.id_apply] }

@[simp]
theorem eq_zero_or_zero_of_dualTensorHom_tmul_eq_zero {f : Dual k V} {x : V}
    [NoZeroSMulDivisors k V] : dualTensorHom k V V (f ⊗ₜ x) = 0 ↔ f = 0 ∨ x = 0 := by
  refine' ⟨fun h => _, fun h => _⟩
  · rcases eq_or_ne x 0 with (rfl | hx); · simp
    left
    ext v
    simp only [LinearMap.zero_apply]
    replace h : f v • x = 0 := by
      simpa only [dualTensorHom_apply, LinearMap.zero_apply] using LinearMap.congr_fun h v
    rw [smul_eq_zero] at h
    tauto
  · rcases h with (rfl | rfl) <;> simp

theorem Unit.apply_root_mem {Φ : Set V} (u : MulAction.stabilizer (V ≃ₗ[k] V) Φ) (x : Φ) :
    u (x : V) ∈ Φ := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨x, hx⟩ := x
  change u x ∈ Φ
  rw [MulAction.mem_stabilizer_iff] at hu
  replace hu : u '' Φ = Φ := by rwa [← image_smul] at hu
  rw [← hu]
  exact mem_image_of_mem u hx

@[simps]
def Unit.toPerm {Φ : Set V} (u : MulAction.stabilizer (V ≃ₗ[k] V) Φ) : Equiv.Perm Φ
    where
  toFun x := ⟨u x, Unit.apply_root_mem u x⟩
  invFun x := ⟨u⁻¹ x, Unit.apply_root_mem u⁻¹ x⟩
  left_inv := by
    intro x
    simp only [Subtype.coe_mk]
    apply Subtype.eq
    simp only [Subtype.val_eq_coe]
    exact (u : V ≃ₗ[k] V).symm_apply_apply x
  right_inv := by
    intro x
    simp only [Subtype.coe_mk]
    ext
    simp only [Subtype.val_eq_coe]
    exact (u : V ≃ₗ[k] V).apply_symm_apply x

@[simps]
def Unit.toPerm' {Φ : Set V} : MulAction.stabilizer (V ≃ₗ[k] V) Φ →* Equiv.Perm Φ
    where
  toFun := Unit.toPerm
  map_one' := by
    ext
    simp only [unit.to_perm_apply_coe, Equiv.Perm.coe_one, id.def]
    rfl
  map_mul' := by
    intro u₁ u₂
    ext
    simp only [unit.to_perm_apply_coe, Equiv.Perm.coe_mul]
    rfl

theorem Unit.injective_toPerm' {Φ : Set V} (hΦ : Submodule.span k Φ = ⊤) :
    Injective (Unit.toPerm' : MulAction.stabilizer (V ≃ₗ[k] V) Φ → Equiv.Perm Φ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hu
  have hu' := FunLike.congr_fun hu
  change ∀ x, _ = x at hu'
  ext v
  change u v = v
  have := FunLike.congr_fun hu
  simp only [unit.to_perm'_apply, Equiv.Perm.coe_one, id.def, SetCoe.forall] at this
  have mem1 : v ∈ Submodule.span k Φ := by
    rw [hΦ]
    exact Submodule.mem_top
  apply Submodule.span_induction mem1
  · intro x hx
    specialize hu' ⟨x, hx⟩
    dsimp [unit.to_perm] at hu'
    simp at hu'
    exact hu'
  · exact LinearEquiv.map_zero _
  · intro x y hx hy
    erw [LinearEquiv.map_add]
    change u x + u y = x + y
    rw [hx, hy]
  · intro t x hx
    erw [LinearEquiv.map_smul]
    change t • u x = t • x
    rw [hx]

theorem finite_stabilizer_of_finite_of_span_eq_top {Φ : Set V} (hΦ₁ : Φ.Finite)
    (hΦ₂ : Submodule.span k Φ = ⊤) : Finite (MulAction.stabilizer (V ≃ₗ[k] V) Φ) :=
  haveI : Fintype Φ := hΦ₁.fintype
  _root_.finite.of_injective unit.to_perm' (unit.injective_to_perm' hΦ₂)

theorem isOfFinOrder_of_finite_of_span_eq_top_of_image_subseteq {Φ : Set V} (hΦ₁ : Φ.Finite)
    (hΦ₂ : Submodule.span k Φ = ⊤) {u : V ≃ₗ[k] V} (hu : u '' Φ ⊆ Φ) : IsOfFinOrder u := by
  replace hu : u '' Φ = Φ
  · haveI : Fintype Φ := finite.fintype hΦ₁
    apply Set.eq_of_subset_of_card_le hu
    rw [Set.card_image_of_injective Φ u.injective]
  let u' : MulAction.stabilizer (V ≃ₗ[k] V) Φ := ⟨u, hu⟩
  have hu' : IsOfFinOrder u ↔ IsOfFinOrder u' := by
    suffices orderOf u = orderOf u' by
      rw [← orderOf_pos_iff]
      have hord : 0 < orderOf u ↔ 0 < orderOf u' := iff_of_eq (congr_arg (LT.lt 0) this)
      rw [hord, orderOf_pos_iff]
    rw [← Subgroup.orderOf_coe u']
    simp only [Subtype.coe_mk]
  rw [hu']
  haveI := finite_stabilizer_of_finite_of_span_eq_top hΦ₁ hΦ₂
  exact isOfFinOrder_of_finite u'

/-- Uniqueness lemma from page 25 of Serre's "Complex semisimple Lie algebras". -/
theorem eq_dual_of_toPreSymmetry_image_subseteq [CharZero k] [NoZeroSMulDivisors k V] {x : V}
    (hx : x ≠ 0) {Φ : Set V} (hΦ₁ : Φ.Finite) (hΦ₂ : Submodule.span k Φ = ⊤) {f g : Dual k V}
    (hf₁ : f x = 2) (hf₂ : toPreSymmetry x f '' Φ ⊆ Φ) (hg₁ : g x = 2)
    (hg₂ : toPreSymmetry x g '' Φ ⊆ Φ) : f = g := by
  let u := to_symmetry hg₁ * to_symmetry hf₁
  suffices IsOfFinOrder u by
    have hu : ↑u = LinearMap.id + dualTensorHom k V V ((f - g) ⊗ₜ x) := by
      ext y
      simp only [to_symmetry, hg₁, LinearMap.toFun_eq_coe, LinearEquiv.coe_hMul,
        LinearMap.mul_apply, LinearEquiv.coe_coe, LinearEquiv.coe_mk, to_pre_symmetry_apply,
        LinearEquiv.map_sub, LinearEquiv.map_smulₛₗ, RingHom.id_apply, LinearMap.add_apply,
        LinearMap.id_coe, id.def, dualTensorHom_apply, LinearMap.sub_apply, map_sub,
        sub_add_cancel', smul_neg, sub_neg_eq_add, sub_smul, two_smul]
      abel
    replace hu : ∀ n : ℕ, ↑(u ^ n) = LinearMap.id + (n : k) • dualTensorHom k V V ((f - g) ⊗ₜ x)
    · intro n
      induction' n with n ih; · simpa
      have aux :
        (dualTensorHom k V V ((f - g) ⊗ₜ[k] x)).comp
            ((n : k) • dualTensorHom k V V ((f - g) ⊗ₜ[k] x)) =
          0 :=
        by ext v; simp [hf₁, hg₁]
      rw [pow_succ, LinearEquiv.coe_hMul, ih, hu, add_mul, mul_add, mul_add]
      simp only [LinearMap.mul_eq_comp, LinearMap.id_comp, LinearMap.comp_id, Nat.cast_succ, aux,
        add_zero, add_smul, one_smul, add_assoc]
    obtain ⟨n, hn₀, hn₁⟩ := (isOfFinOrder_iff_pow_eq_one u).mp this
    specialize hu n
    replace hn₁ : (↑(u ^ n) : V →ₗ[k] V) = LinearMap.id := linear_equiv.to_linear_map_inj.mpr hn₁
    simpa only [hn₁, smul_eq_zero, Nat.cast_eq_zero, hn₀.ne', false_or_iff, or_false_iff, hx,
      eq_zero_or_zero_of_dual_tensor_hom_tmul_eq_zero, sub_eq_zero, self_eq_add_right] using hu
  suffices u '' Φ ⊆ Φ by
    exact is_of_fin_order_of_finite_of_span_eq_top_of_image_subseteq hΦ₁ hΦ₂ this
  change to_pre_symmetry x g ∘ to_pre_symmetry x f '' Φ ⊆ Φ
  rw [image_comp]
  exact (monotone_image hf₂).trans hg₂

#print Module.subsingleton_dual_iff /-
-- V dual is zero if and only if V is zero --
@[simp]
theorem subsingleton_dual_iff {k V : Type _} [Field k] [AddCommGroup V] [Module k V] :
    Subsingleton (Dual k V) ↔ Subsingleton V := by
  refine' ⟨fun h => ⟨fun v w => _⟩, fun h => ⟨fun f g => _⟩⟩
  · rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff k (v - w)]
    intro f
    simp [@Subsingleton.elim _ h f 0]
  · ext v
    simp [@Subsingleton.elim _ h v 0]
-/

#print Module.nontrivial_dual_iff /-
@[simp]
theorem nontrivial_dual_iff {k V : Type _} [Field k] [AddCommGroup V] [Module k V] :
    Nontrivial (Dual k V) ↔ Nontrivial V := by
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton,
    subsingleton_dual_iff]
-/

#print QuadraticForm.toQuadraticForm_polarBilin /-
-- May or may not need this.
@[simp]
theorem QuadraticForm.toQuadraticForm_polarBilin (Q : QuadraticForm k V) :
    Q.polarBilin.toQuadraticForm = (2 : k) • Q := by ext; simp
-/

-- May or may not need this.
@[simp]
theorem BilinForm.toQuadraticForm.polarBilin {B : BilinForm k V} (h : B.IsSymm) :
    B.toQuadraticForm.polarBilin = (2 : k) • B := by
  ext v w
  erw [QuadraticForm.polarBilin_apply, BilinForm.smul_apply, BilinForm.polar_toQuadraticForm,
    h.eq w v, two_smul]

/-- Given a representation of a finite group on a space carrying a bilinear form, we can take
the average to obtain an invariant bilinear form.

The API for `finsum` should be expanded to interact well with `finite`. This would make the proofs
below trivial. -/
def averageBilinear {G : Type _} [Group G] [Finite G] (ρ : G →* V ≃ₗ[k] V) (B : V →ₗ[k] Dual k V) :
    V →ₗ[k] Dual k V
    where
  toFun v := ∑ᶠ g, (B (ρ g • v)).comp (ρ g : V →ₗ[k] V)
  map_add' v w := by
    rw [← finsum_add_distrib _]
    · simp only [smul_add, map_add, LinearMap.add_comp]
    · apply Set.toFinite
    · apply Set.toFinite
  map_smul' t v := by
    haveI : Fintype G := Fintype.ofFinite G
    simp only [finsum_eq_sum_of_fintype, RingHom.id_apply, Finset.smul_sum]
    congr
    ext g w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, LinearEquiv.smul_def,
      LinearEquiv.map_smulₛₗ, RingHom.id_apply]

theorem averageBilinear_apply_apply {G : Type _} [Group G] [Finite G] (ρ : G →* V ≃ₗ[k] V)
    (B : V →ₗ[k] Dual k V) (v w : V) : averageBilinear ρ B v w = ∑ᶠ g, B (ρ g • v) (ρ g • w) := by
  haveI : Fintype G := Fintype.ofFinite G
  simpa only [average_bilinear, LinearMap.coe_mk, finsum_eq_sum_of_fintype, LinearMap.coeFn_sum,
    LinearMap.coe_comp, Finset.sum_apply, comp_app]

@[simp]
theorem QuadraticForm.comp_posDef_iff {k V : Type _} [LinearOrderedField k] [AddCommGroup V]
    [Module k V] (Q : QuadraticForm k V) (g : V ≃ₗ[k] V) :
    (Q.comp (g : V →ₗ[k] V)).PosDef ↔ Q.PosDef := by
  suffices ∀ (Q : QuadraticForm k V) (g : V ≃ₗ[k] V), Q.PosDef → (Q.comp (g : V →ₗ[k] V)).PosDef by
    refine' ⟨fun hQ => _, this Q g⟩
    convert this (Q.comp (g : V →ₗ[k] V)) g⁻¹ hQ
    ext v
    simp_rw [QuadraticForm.comp_apply, ← LinearMap.comp_apply, ← LinearMap.mul_eq_comp]
    change Q v = Q ((g * g⁻¹) v)
    simp
  clear Q g; intro Q g hQ v hv
  replace hv : g v ≠ 0
  · contrapose! hv
    replace hv : (↑g⁻¹ : V →ₗ[k] V).comp (↑g : V →ₗ[k] V) v = (↑g⁻¹ : V →ₗ[k] V) 0 :=
      LinearMap.congr_arg hv
    simpa [← LinearMap.mul_eq_comp] using hv
  simp only [QuadraticForm.comp_apply]
  exact hQ _ hv

-- Can avoid proving this lemma if we delete `average_bilinear` and just use
-- `∑ᶠ g, B.to_bilin.to_quadratic_form.comp (ρ g)` instead
theorem averageBilinear_eq_sum {G : Type _} [Group G] [Finite G] (ρ : G →* V ≃ₗ[k] V)
    (B : V →ₗ[k] Dual k V) :
    (averageBilinear ρ B).toBilin.toQuadraticForm =
      ∑ᶠ g, B.toBilin.toQuadraticForm.comp (ρ g : V →ₗ[k] V) := by
  ext v
  haveI : Fintype G := Fintype.ofFinite G
  simp only [average_bilinear, LinearMap.coe_mk, finsum_eq_sum_of_fintype, LinearMap.coeFn_sum,
    LinearMap.coe_comp, Finset.sum_apply, comp_app, BilinForm.toQuadraticForm_apply,
    QuadraticForm.sum_apply, QuadraticForm.comp_apply]
  change (∑ g, (B (ρ g • v)).comp ↑(ρ g)) v = ∑ g, B (ρ g v) (ρ g v)
  -- TODO Should be via `simp`
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.coe_comp, comp_app]
  rfl

-- TODO Should be via `simp`
@[simp]
theorem averageBilinear_smul_smul {G : Type _} [Group G] [Finite G] (ρ : G →* V ≃ₗ[k] V)
    (B : V →ₗ[k] Dual k V) (v w : V) (g : G) :
    averageBilinear ρ B (ρ g • v) (ρ g • w) = averageBilinear ρ B v w := by
  simp only [average_bilinear_apply_apply, smul_smul, ← map_mul]
  let b : G → k := fun g' => B (ρ g' • v) (ρ g' • w)
  let e : G ≃ G := Equiv.mulRight g
  change ∑ᶠ g', (b ∘ e) g' = ∑ᶠ g', b g'
  exact finsum_comp_equiv e

-- A better version of `basis.to_dual_total_left` which we'll need.
@[simp]
theorem Basis.toDual_total_left' {R M ι : Type _} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] (b : Basis ι R M) (f : ι →₀ R) : b.toDual (Finsupp.total ι M R b f) ∘ b = f :=
  by ext i; simp only [Function.comp_apply]; simp

theorem Basis.toDual_posDef {k V ι : Type _} [LinearOrderedField k] [AddCommGroup V] [Module k V]
    (b : Basis ι k V) : b.toDual.toBilin.toQuadraticForm.PosDef := by
  intro v hv
  simp only [BilinForm.toQuadraticForm_apply]
  change 0 < b.to_dual v v
  -- TODO Should be via `simp`.
  replace hv : (b.repr v).support.Nonempty;
  · contrapose! hv; simpa using hv
  rw [← b.total_repr v, Finsupp.apply_total, b.to_dual_total_left', Finsupp.total_apply]
  apply Finset.sum_pos
  rintro i hi
  simp only [Finsupp.mem_support_iff] at hi
  simp only [Algebra.id.smul_eq_mul, mul_self_pos, Ne.def]
  exact hi
  exact hv

theorem QuadraticForm.PosDef.sum {k V ι : Type _} [Finite ι] [Nonempty ι] [LinearOrderedField k]
    [AddCommGroup V] [Module k V] (q : ι → QuadraticForm k V) (hq : ∀ i, (q i).PosDef) :
    (∑ᶠ i, q i).PosDef := by
  haveI : Fintype ι := Fintype.ofFinite ι
  simp only [finsum_eq_sum_of_fintype]
  refine'
    Finset.sum_induction_nonempty _ _ (fun a b ha hb => QuadraticForm.PosDef.add _ _ ha hb)
      Finset.univ_nonempty fun i hi => hq _

theorem LinearMap.toBilin.PosDef.ker_eq_bot {k V : Type _} [LinearOrderedField k] [AddCommGroup V]
    [Module k V] (b : V →ₗ[k] Dual k V) (hb : b.toBilin.toQuadraticForm.PosDef) : b.ker = ⊥ := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  refine' ⟨fun hv => _, fun hv => _⟩
  · rw [← hb.anisotropic.eq_zero_iff]
    simp only [BilinForm.toQuadraticForm_apply]
    change b v v = 0
    -- TODO Should be via `simp`
    rw [hv]
    simp
  · rw [hv]
    simp

/-- The assumption `linear_ordered_field` is stronger than necessary but enables an easy proof
by just taking the average of a positive definite bilinear form. -/
theorem exists_to_dual_ker_eq_bot {k V G : Type _} [LinearOrderedField k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Group G] [Finite G] (ρ : G →* V ≃ₗ[k] V) :
    ∃ B : V →ₗ[k] Dual k V, B.ker = ⊥ ∧ ∀ (v w) (g : G), B (ρ g • v) (ρ g • w) = B v w := by
  obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis k V
  refine' ⟨average_bilinear ρ b.to_dual, _, fun v w g => by simp only [average_bilinear_smul_smul]⟩
  apply LinearMap.toBilin.PosDef.ker_eq_bot
  rw [average_bilinear_eq_sum]
  apply QuadraticForm.PosDef.sum
  intro g
  rw [QuadraticForm.comp_posDef_iff]
  convert b.to_dual_pos_def

/- Possible alternative approach if seek to drop `average_bilinear`:
  let Q : quadratic_form k V := ∑ᶠ g, b.to_dual.to_bilin.to_quadratic_form.comp (ρ g : V →ₗ[k] V),
  refine ⟨Q.polar_bilin.to_lin, _, λ v w g, _⟩,
  { apply linear_map.to_bilin.pos_def.ker_eq_bot,
    change Q.polar_bilin.to_quadratic_form.pos_def, -- TODO Should be via `simp`
    simp only [quadratic_form.to_quadratic_form_polar_bilin],
    refine quadratic_form.pos_def.smul _ (two_pos : 0 < (2 : k)),
    apply quadratic_form.pos_def.sum,
    intros g,
    rw quadratic_form.comp_pos_def_iff,
    convert b.to_dual_pos_def, },
  { change Q.polar_bilin (ρ g v) (ρ g w) = Q.polar_bilin v w, -- TODO Should be via `simp`
    admit, },
  -/
end Module

namespace Submodule

variable {k V : Type _} [Field k] [AddCommGroup V] [Module k V] {p : Submodule k V}

#print Submodule.exists_dual_map_eq_bot_of_lt_top /-
-- For any proper submodule there exists a non-zero linear form vanishing on it
theorem exists_dual_map_eq_bot_of_lt_top (hp : p < ⊤) :
    ∃ f : Module.Dual k V, f ≠ 0 ∧ p.map f = ⊥ := by
  replace hp : Nontrivial (Module.Dual k <| V ⧸ p) :=
    module.nontrivial_dual_iff.mpr (quotient.nontrivial_of_lt_top p hp)
  obtain ⟨f, g, h⟩ := hp
  replace h : f - g ≠ 0 := sub_ne_zero.mpr h
  refine' ⟨(f - g).comp p.mkq, _, by simp [map_comp]⟩
  contrapose! h
  refine' p.quot_hom_ext fun v => _
  change (f - g).comp p.mkq v = _
  simp [h]
-/

end Submodule
