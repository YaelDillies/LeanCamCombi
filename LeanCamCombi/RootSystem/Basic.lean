import LeanCamCombi.RootSystem.LinearAlgebraAux
import LeanCamCombi.RootSystem.Misc

noncomputable section

open Set Function

open scoped Pointwise

/-- A crystallographic root system (possibly non-reduced). -/
@[protect_proj]
class IsRootSystem (k : Type _) {V : Type _} [CommRing k] [CharZero k] [AddCommGroup V] [Module k V]
    (Φ : Set V) : Prop where
  Finite : Φ.Finite
  span_eq_top : Submodule.span k Φ = ⊤
  exists_dual : ∀ α ∈ Φ, ∃ f : Module.Dual k V, f α = 2 ∧ Module.toPreSymmetry α f '' Φ ⊆ Φ
  subset_zmultiples :
    ∀ α ∈ Φ,
      ∀ (f : Module.Dual k V),
        f α = 2 ∧ Module.toPreSymmetry α f '' Φ ⊆ Φ → f '' Φ ⊆ AddSubgroup.zmultiples (1 : k)

namespace IsRootSystem

variable {k V : Type _} [CommRing k] [CharZero k] [AddCommGroup V] [Module k V]
  [NoZeroSMulDivisors k V]

variable {Φ : Set V} (h : IsRootSystem k Φ)

/-- The coroot of a root.

Note that although this uses `classical.some`, the choice is unique (see Serre's lemma). -/
def coroot (α : Φ) : Module.Dual k V :=
  Classical.choose <| h.exists_dual _ α.property

local postfix:100 "ᘁ" => h.coroot

@[simp]
theorem coroot_apply_self_eq_two (α : Φ) : (αᘁ) α = 2 :=
  (Classical.choose_spec (h.exists_dual _ α.property)).1

@[simp]
theorem coroot_toPreSymmetry_subset (α : Φ) : Module.toPreSymmetry (α : V) (αᘁ) '' Φ ⊆ Φ :=
  (Classical.choose_spec (h.exists_dual _ α.property)).2

-- lemma root_ne_zero (α : Φ) : (α : V) ≠ 0 :=
-- λ contra, by simpa [contra] using h.coroot_apply_self_eq_two α
theorem root_ne_zero (α : Φ) : (α : V) ≠ 0 := by
  intro contra
  have := h.coroot_apply_self_eq_two α
  -- simp only [coroot_apply_self_eq_two, eq_self_iff_true] at this,
  rw [contra, LinearMap.map_zero] at this
  norm_num at this

theorem zero_not_mem : (0 : V) ∉ Φ := fun contra => h.root_ne_zero ⟨0, contra⟩ rfl

/-- The symmetry associated to a root. -/
def symmetryOfRoot (α : Φ) : V ≃ₗ[k] V :=
  Module.toSymmetry <| h.coroot_apply_self_eq_two α

local notation "ട" => h.symmetryOfRoot

theorem symmetryOfRoot_apply (α : Φ) (v : V) : ട α v = v - (αᘁ) v • α :=
  Module.toPreSymmetry_apply (α : V) v (αᘁ)

@[simp]
theorem symmetryOfRoot_apply_self_neg (α : Φ) : ട α α = -α :=
  Module.toPreSymmetry_apply_self <| h.coroot_apply_self_eq_two α

@[simp]
theorem symmetryOfRoot_sq (α : Φ) : ട α ^ 2 = 1 := by
  ext v
  have := Module.toPreSymmetry_sq (coroot_apply_self_eq_two h α)
  exact LinearMap.congr_fun this v

-- protected lemma finite_dimensional : finite_dimensional k V :=
-- ⟨⟨h.finite.to_finset, by simpa only [finite.coe_to_finset] using h.span_eq_top⟩⟩
theorem symmetryOfRoot_image_subset (α : Φ) : ട α '' Φ ⊆ Φ :=
  (Classical.choose_spec (h.exists_dual _ α.property)).2

@[simp]
theorem symmetryOfRoot_image_eq (α : Φ) : ട α '' Φ = Φ := by
  refine' subset_antisymm (h.symmetry_of_root_image_subset α) _
  have : Φ = ട α ∘ ട α '' Φ := by change Φ = ⇑(ട α ^ 2) '' Φ; simp
  conv_lhs => rw [this, image_comp]
  mono
  exact h.symmetry_of_root_image_subset α

@[simp]
theorem symmetryOfRoot_apply_mem (α β : Φ) : ട α β ∈ Φ := by
  apply h.symmetry_of_root_image_subset α
  simp only [mem_image]
  exact ⟨β, β.property, rfl⟩

@[simp]
theorem neg_mem (α : Φ) : -(α : V) ∈ Φ := by
  have := (image_subset_iff.mp <| h.symmetry_of_root_image_subset α) α.property
  simpa only [Subtype.val_eq_coe, mem_preimage, symmetry_of_root_apply_self_neg] using this

@[simp]
theorem coroot_image_subset_zmultiples (α : Φ) : αᘁ '' Φ ⊆ AddSubgroup.zmultiples (1 : k) :=
  h.subset_zmultiples α α.property (αᘁ)
    ⟨h.coroot_apply_self_eq_two α, h.symmetryOfRoot_image_subset α⟩

@[simp]
theorem coroot_apply_mem_zmultiples (α β : Φ) : (αᘁ) β ∈ AddSubgroup.zmultiples (1 : k) := by
  have := (image_subset_iff.mp <| h.coroot_image_subset_zmultiples α) β.property
  simpa using this

@[simp]
theorem coroot_apply_mem_zmultiples_2 (α β : Φ) : ∃ a : ℤ, (αᘁ) β = a := by
  have hr := h.coroot_apply_mem_zmultiples α β
  rw [AddSubgroup.mem_zmultiples_iff] at hr
  simp only [Int.smul_one_eq_coe] at hr
  obtain ⟨a, ha⟩ := hr
  exact ⟨a, ha.symm⟩

theorem exists_int_coroot_apply_eq (α β : Φ) : ∃ n : ℤ, (αᘁ) β = n := by
  obtain ⟨n, hn⟩ := add_subgroup.mem_zmultiples_iff.mp (h.coroot_apply_mem_zmultiples α β)
  rw [← hn]
  exact ⟨n, by simp⟩

theorem eq_coroot_of_toPreSymmetry_image_subseteq (α : Φ) (f : Module.Dual k V) (hf₁ : f α = 2)
    (hf₂ : Module.toPreSymmetry (α : V) f '' Φ ⊆ Φ) : f = αᘁ :=
  Module.eq_dual_of_toPreSymmetry_image_subseteq (h.root_ne_zero α) h.Finite h.span_eq_top hf₁ hf₂
    (h.coroot_apply_self_eq_two α) (h.symmetryOfRoot_image_subset α)

/-- The group of symmetries of a root system.

TODO: Define equivalences of root systems more generally and thus obtain this as the
self-equivalences of a single root system. -/
def symmetries : Subgroup (V ≃ₗ[k] V) :=
  MulAction.stabilizer (V ≃ₗ[k] V) Φ

def isRootSystemEquiv {V₂ : Type _} [AddCommGroup V₂] [Module k V₂] {Φ₂ : Set V₂}
    (h₂ : IsRootSystem k Φ₂) :=
  {e : V ≃ₗ[k] V₂ | e '' Φ = Φ₂}

theorem symm_equiv {α β : Type _} (f : α ≃ β) (s : Set α) (d : Set β) (h : f '' s = d) :
    f.symm '' d = s := by
  rw [← h]
  rw [Equiv.symm_image_image]

theorem symm_root_system_equiv {V₂ : Type _} [AddCommGroup V₂] [Module k V₂]
    [NoZeroSMulDivisors k V₂] {Φ₂ : Set V₂} (h₂ : IsRootSystem k Φ₂) (e : V ≃ₗ[k] V₂)
    (he : e ∈ h.isRootSystemEquiv h₂) : e.symm ∈ h₂.isRootSystemEquiv h := by
  -- rw set.mem_iff at he,
  suffices e.symm '' Φ₂ = Φ by refine' this
  exact symm_equiv e.to_equiv _ _ he

-- prove symm
def isRootSystemEquivSymm {V₂ : Type _} [AddCommGroup V₂] [Module k V₂] [NoZeroSMulDivisors k V₂]
    {Φ₂ : Set V₂} (h₂ : IsRootSystem k Φ₂) : isRootSystemEquiv h h₂ → isRootSystemEquiv h₂ h := by
  rintro ⟨e, he⟩
  refine' ⟨e.symm, _⟩
  exact symm_root_system_equiv h h₂ e he

@[simp]
theorem mem_symmetries_iff (u : V ≃ₗ[k] V) : u ∈ h.symmetries ↔ u '' Φ = Φ :=
  Iff.rfl

theorem finite_symmetries : Finite h.symmetries :=
  by-- Should follow from `module.finite_stabilizer_of_finite_of_span_eq_top`
  apply Module.finite_stabilizer_of_finite_of_span_eq_top h.finite h.span_eq_top

-- reflections are invertible endomorphisms and sit in the endomorphism ring
-- i.e. they are all units in the automorphism group
/-- The Weyl group of a root system. -/
def weylGroup : Subgroup (V ≃ₗ[k] V) :=
  Subgroup.closure <| range h.symmetryOfRoot

theorem weylGroup_le_symmetries : h.weylGroup ≤ h.symmetries := by
  -- Should be easy via `subgroup.closure_le`
  unfold weyl_group
  rw [Subgroup.closure_le h.symmetries]
  rintro - ⟨α, rfl⟩
  exact h.symmetry_of_root_image_eq α

@[simp]
theorem symmetry_mem_weylGroup (α : Φ) : ട α ∈ h.weylGroup :=
  Subgroup.subset_closure <| mem_range_self α

-- w acts on α and sends roots to roots (acts on roots)
-- w acting on α gives a root, not a random vector
theorem weylGroup_apply_root_mem (w : h.weylGroup) (α : Φ) : w • (α : V) ∈ Φ := by
  obtain ⟨w, hw⟩ := w
  change w • (α : V) ∈ Φ
  revert α
  have : ∀ g : V ≃ₗ[k] V, g ∈ range h.symmetry_of_root → ∀ α : Φ, g • (α : V) ∈ Φ := by
    rintro - ⟨β, rfl⟩ α; exact h.symmetry_of_root_image_subset β ⟨α, α.property, rfl⟩
  -- Look up what this means
  refine' Subgroup.closure_induction hw this _ (fun g₁ g₂ hg₁ hg₂ α => _) fun g hg α => _
  · simp
  · rw [mul_smul]; exact hg₁ ⟨_, hg₂ α⟩
  · let e : V ≃ V := ⟨fun x => g • x, fun x => g.symm • x, fun x => by simp, fun x => by simp⟩
    exact e.symm_apply_mem_of_forall_mem_finite hg h.finite α

@[simps]
def weylGroupToPerm (w : h.weylGroup) : Equiv.Perm Φ
    where
  toFun α := ⟨w • (α : V), h.weylGroup_apply_root_mem w α⟩
  invFun α := ⟨w⁻¹ • (α : V), h.weylGroup_apply_root_mem w⁻¹ α⟩
  left_inv α := by simp
  right_inv α := by simp

/-- TODO (optional) Now that we have the more general version of this used to prove
`module.is_of_fin_order_of_finite_of_span_eq_top_of_image_subseteq`, consider reimplementing this as
`module.unit.to_perm'.comp $ subgroup.inclusion h.weyl_group_le_symmetries`. -/
@[simps]
def weylGroupToPerm' : h.weylGroup →* Equiv.Perm Φ
    where
  toFun := h.weylGroupToPerm
  map_one' := by
    ext
    simp [weyl_group_to_perm]
  map_mul' := by
    intro α β
    ext
    simp [weyl_group_to_perm, mul_smul]

def weylGroupToPerm'' : h.weylGroup →* Equiv.Perm Φ :=
  Module.Unit.toPerm'.comp <| Subgroup.inclusion h.weylGroup_le_symmetries

example {α β γ : Type _} (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by refine' injective.comp hg hf

/-- TODO (optional) If we redefine `weyl_group_to_perm'` above then this should be easy using
`module.unit.injective_to_perm'` and `weyl_group_le_symmetries`. -/
theorem injective_weylGroup_to_perm' : Injective h.weylGroupToPerm'' :=
  Injective.comp (Module.Unit.injective_toPerm' h.span_eq_top)
    (Subgroup.inclusion_injective (weylGroup_le_symmetries h))

/-- TODO (optional) If we redefine `weyl_group_to_perm'` above then this should be easy using
`module.unit.injective_to_perm'` and `weyl_group_le_symmetries`. -/
theorem injective_weylGroup_to_perm : Injective h.weylGroupToPerm' := by
  rw [← MonoidHom.ker_eq_bot_iff]
  -- Injective is the same as ker = ⊥
  rw [eq_bot_iff]
  intro w hw
  -- Let w ∈ ker f
  rw [Subgroup.mem_bot]
  -- w ∈ ⊥ ↔ w = 1
  rw [MonoidHom.mem_ker] at hw
  -- x ∈ ker f ↔ f x = 1
  have hw' := FunLike.congr_fun hw
  --Functions are equal if that agree for all values
  change ∀ x, _ = x at hw'
  ext v
  change w v = v
  have := FunLike.congr_fun hw
  simp only [weyl_group_to_perm'_apply, Equiv.Perm.coe_one, id.def, SetCoe.forall] at this
  have mem1 : v ∈ Submodule.span k Φ := by
    rw [h.span_eq_top]
    trivial
  apply Submodule.span_induction mem1
  · intro x hx
    specialize hw' ⟨x, hx⟩
    dsimp [weyl_group_to_perm, (· • ·)] at hw'
    simp at hw'
    exact hw'
  · exact LinearEquiv.map_zero _
  · intro x y hx hy
    erw [LinearEquiv.map_add]
    change w x + w y = x + y
    rw [hx, hy]
  · intro t x hx
    erw [LinearEquiv.map_smul]
    change t • w x = t • x
    rw [hx]

example (G : Type _) [Group G] (H : Subgroup G) [Finite G] : Finite H := by
  refine' Subgroup.finite H

-- example (G : Type*) (H : Type*) [group G] [group H] (h : H ≤ G) [finite G]: finite H := sorry
-- We should really be using `subgroup.of_le` but this is not present in mathlib (analogous to
-- `submodule.of_le`)
/-- TODO Consider reproving this using just `weyl_group_le_symmetries` and `finite_symmetries`
above (i.e., the Weyl group is contained in the subgroup of symmetries which is finite and so it
must be finite). -/
theorem finite_weylGroup : Finite h.weylGroup := by
  suffices Finite h.symmetries by
    let f : h.weyl_group → h.symmetries := fun x => ⟨x, h.weyl_group_le_symmetries x.property⟩
    have hf : injective f := by rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy; simpa using hxy
    haveI := this
    exact Finite.of_injective f hf
  apply finite_symmetries

-- suffices : finite (equiv.perm Φ),
-- { haveI := this,
--   exact finite.of_injective _ h.injective_weyl_group_to_perm, },
-- haveI : finite Φ := finite_coe_iff.mpr h.finite,
-- exact equiv.finite_left,
/-- TODO (optional): use this to golf `is_root_system.coroot_symmetry_apply_eq`. -/
theorem coroot_apply_of_mem_symmetries (u : V ≃ₗ[k] V) (hu : u ∈ h.symmetries) (α : Φ) (h') :
    ⟨u α, h'⟩ᘁ = u.symm.dualMap (αᘁ) := by
  have h₀ : u '' Φ = Φ := hu
  have h₁ : u.symm '' Φ = Φ := by conv_lhs => rw [← h₀, ← image_comp]; simp
  refine' (h.eq_coroot_of_to_pre_symmetry_image_subseteq ⟨u α, h'⟩ _ _ _).symm
  · simp
  · have : Module.toPreSymmetry (u α) (u.symm.dual_map (αᘁ)) = u * ട α * u.symm := by ext v;
      simp [h.symmetry_of_root_apply]
    rw [Subtype.coe_mk, this, LinearMap.mul_eq_comp, LinearMap.mul_eq_comp, LinearMap.coe_comp,
      LinearMap.coe_comp, image_comp, image_comp, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, h₁, h.symmetry_of_root_image_eq α, h₀]

theorem symmetryOfRoot_apply_of_mem_symmetries (u : V ≃ₗ[k] V) (hu : u ∈ h.symmetries) (α : Φ)
    (h') : ട ⟨u α, h'⟩ = u * ട α * u.symm := by
  ext v
  erw [LinearMap.mul_apply]
  rw [h.symmetry_of_root_apply, coroot_apply_of_mem_symmetries]
  simp only [Subtype.coe_mk, LinearEquiv.coe_toLinearMap]
  rw [h.symmetry_of_root_apply]
  simp only [LinearEquiv.map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.map_smulₛₗ,
    RingHom.id_apply, sub_right_inj]
  congr
  exact hu

end IsRootSystem
