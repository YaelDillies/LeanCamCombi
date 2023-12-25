import Mathlib.LinearAlgebra.Finsupp
import LeanCamCombi.RootSystem.Basic

open Set Function

namespace IsRootSystem

variable {k V : Type _} [LinearOrderedField k] [CharZero k] [AddCommGroup V] [Module k V]

variable {Φ : Set V} (h : IsRootSystem k Φ)

local postfix:100 "ᘁ" => h.coroot

local notation "ട" => h.symmetryOfRoot

protected theorem finiteDimensional : FiniteDimensional k V :=
  ⟨⟨h.Finite.toFinset, by simpa only [finite.coe_to_finset] using h.span_eq_top⟩⟩

@[simp]
theorem coroot_symmetry_apply_eq (α β : Φ) (h') : ⟨ട α β, h'⟩ᘁ = βᘁ - (βᘁ) α • αᘁ := by
  set γ : Φ := ⟨ട α β, h'⟩
  have hγ : Module.toPreSymmetry (γ : V) (βᘁ - (βᘁ) α • αᘁ) = ട α * ട β * ട α := by
    ext v
    simp only [Subtype.coe_mk, Module.toPreSymmetry_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.mul_apply]
    -- TODO It should be possibly to fold the `erw` into the `simp only` by sorting out simp-normal
    -- form for various coercions.
    erw [h.symmetry_of_root_apply, h.symmetry_of_root_apply, h.symmetry_of_root_apply,
      h.symmetry_of_root_apply]
    simp only [map_sub, LinearMap.map_smulₛₗ, RingHom.id_apply, Algebra.id.smul_eq_mul,
      coroot_apply_self_eq_two, smul_smul, mul_sub, sub_mul, sub_smul, smul_sub, mul_two, add_smul,
      mul_comm ((βᘁ) α) ((αᘁ) v)]
    abel
    sorry
  have hγ₀ : (γ : V) ≠ 0 := by intro contra; apply h.zero_not_mem; rw [← contra]; exact γ.property
  apply Module.eq_dual_of_toPreSymmetry_image_subseteq hγ₀ h.finite h.span_eq_top
  -- f, g implicit
  · exact h.coroot_apply_self_eq_two γ
  · exact h.coroot_to_pre_symmetry_subset γ
  · simp only [symmetry_of_root_apply, mul_sub, Subtype.coe_mk, LinearMap.sub_apply, map_sub,
      coroot_apply_self_eq_two, LinearMap.map_smulₛₗ, RingHom.id_apply, Algebra.id.smul_eq_mul,
      LinearMap.smul_apply]
    ring
  · rw [hγ]
    change ട α ∘ ട β ∘ ട α '' Φ ⊆ Φ
    rw [← comp.assoc]
    simp only [image_comp, h.symmetry_of_root_image_eq]

theorem finite_coroots : (range h.coroot).Finite :=
  @Set.finite_range _ _ h.coroot <| finite_coe_iff.mpr h.Finite

/-- An auxiliary result used only to prove `is_root_system.coroot_span_eq_top`.

Note that `is_root_system.to_dual` shows that any root system carries a _canonical_ non-singular
invariant bilinear form. This lemma only exists because we need it to prove the coroots span the
dual space which we use to show `is_root_system.to_dual` is non-singular. -/
theorem exists_to_dual_ker_eq_bot_forall :
    ∃ B : V →ₗ[k] V →ₗ[k] k, B.ker = ⊥ ∧ ∀ (v w) (α : Φ), B (ട α v) (ട α w) = B v w := by
  haveI := h.finite_dimensional
  haveI : Finite h.weyl_group := h.finite_weyl_group
  obtain ⟨B, hB₁, hB₂⟩ := Module.exists_to_dual_ker_eq_bot h.weyl_group.subtype
  exact ⟨B, hB₁, fun v w α => hB₂ v w ⟨ട α, h.symmetry_mem_weyl_group α⟩⟩

theorem coroot_eq_zero_only_if_v_eq_zero : ∀ (v : V) (h' : ∀ α : Φ, h.coroot α v = 0), v = 0 := by
  intro v hv
  obtain ⟨B, h1, h2⟩ := h.exists_to_dual_ker_eq_bot_forall
  replace hv : ∀ α, ട α v = v
  · intro α
    rw [h.symmetry_of_root_apply, hv, zero_smul, sub_zero]
  specialize h2 v
  simp_rw [hv] at h2
  replace h2 : ∀ α : Φ, (B v) ((h.symmetry_of_root α) α) = (B v) α
  · intro α
    rw [h2]
  simp only [symmetry_of_root_apply_self_neg, map_neg, SetCoe.forall, Subtype.coe_mk,
    neg_eq_self_iff] at h2
  have h3 : ∀ α : Φ, (B v) α = 0 := fun x => h2 x.1 x.2
  have h4 : B v = 0 := by
    ext α
    change (B v) α = 0
    have h5 : α ∈ Submodule.span k Φ := by
      rw [h.span_eq_top]
      exact Submodule.mem_top
    rw [mem_span_set] at h5
    rcases h5 with ⟨c, hc, rfl⟩
    simp only [map_finsupp_sum, LinearMap.map_smulₛₗ, RingHom.id_apply, Algebra.id.smul_eq_mul]
    refine' Finset.sum_eq_zero fun p hp => _
    dsimp
    specialize h3 ⟨p, hc (finset.mem_coe.mp hp)⟩
    simp only [mul_eq_zero]
    exact Or.intro_right _ h3
  rw [LinearMap.ker_eq_bot] at h1
  refine' h1 _
  rw [LinearMap.map_zero]
  exact h4

theorem coroot_span_eq_top : Submodule.span k (range h.coroot) = ⊤ := by
  suffices ∀ (v : V) (h' : ∀ α : Φ, h.coroot α v = 0), v = 0 by
    contrapose! this
    rw [← lt_top_iff_ne_top] at this
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top this
    haveI := h.finite_dimensional
    refine'
      ⟨(Module.evalEquiv k V).symm f, fun α => _, by
        simpa only [Ne.def, LinearEquiv.map_eq_zero_iff]⟩
    simp only [Module.apply_evalEquiv_symm_apply, ← Submodule.mem_bot k, ← hf', Submodule.mem_map]
    refine' ⟨h.coroot α, _, rfl⟩
    apply Submodule.subset_span
    exact mem_range_self α
  exact h.coroot_eq_zero_only_if_v_eq_zero

theorem fd {k V : Type _} [LinearOrderedField k] [CharZero k] [AddCommGroup V] [Module k V]
    {Φ : Set V} (h : IsRootSystem k Φ) (α : ↥Φ) [_inst : FiniteDimensional k V] :
    ⇑(Module.toPreSymmetry (h.coroot α) ((Module.evalEquiv k V) ↑α)) '' range h.coroot ⊆
      range h.coroot := by
  simp only [Module.toPreSymmetry_apply, image_subset_iff]
  rintro y ⟨β, rfl⟩
  simp
  exact ⟨ട α β, h.symmetry_of_root_apply_mem α β, h.coroot_symmetry_apply_eq α β _⟩

/-- A root system in `V` naturally determines another root system in the dual `V^*`. -/
theorem isRootSystemCoroots : IsRootSystem k <| range h.coroot :=
  { Finite := h.finite_coroots
    span_eq_top := h.coroot_span_eq_top
    exists_dual := by
      rintro x ⟨α, rfl⟩
      refine' ⟨Module.Dual.eval k V α, by simp, _⟩
      simp only [Module.toPreSymmetry_apply, Module.Dual.eval_apply, image_subset_iff]
      rintro y ⟨β, rfl⟩
      simp only [mem_preimage, mem_range, SetCoe.exists]
      exact ⟨ട α β, h.symmetry_of_root_apply_mem α β, h.coroot_symmetry_apply_eq α β _⟩
    subset_zmultiples := by
      rintro aux ⟨α, rfl⟩ α' ⟨h₁, h₂⟩ - ⟨-, ⟨β, rfl⟩, rfl⟩
      have hα : h.coroot α ≠ 0 := by
        intro h
        simp only [h, LinearMap.map_zero] at h₁
        norm_num at h₁
      haveI := h.finite_dimensional
      rw [Module.eq_dual_of_toPreSymmetry_image_subseteq hα h.finite_coroots h.coroot_span_eq_top h₁
          h₂ (_ : Module.evalEquiv k V α (h.coroot α) = 2) _]
      · refine'
          h.subset_zmultiples β β.property (h.coroot β) ⟨h.coroot_apply_self_eq_two β, _⟩
            ⟨α, α.property, rfl⟩
        exact h.symmetry_of_root_image_subset β
      · exact h.coroot_apply_self_eq_two α
      · apply fd }

end IsRootSystem
