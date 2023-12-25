import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.Quaternion
import LeanCamCombi.RootSystem.Basic

noncomputable section

variable {V : Type _} [AddCommGroup V] [Module ℝ V]

open scoped Quaternion RealInnerProductSpace Pointwise

local notation "e₁" => QuaternionAlgebra.mk 1 0 0 0

-- `1`
local notation "e₂" => QuaternionAlgebra.mk 0 1 0 0

-- `i`
local notation "e₃" => QuaternionAlgebra.mk 0 0 1 0

-- `j`
local notation "e₄" => QuaternionAlgebra.mk 0 0 0 1

-- `k`
def s : ℍ[ℝ] :=
  QuaternionAlgebra.mk (1 / 2) (1 / 2) (1 / 2) (1 / 2)

/-- Lipshitz quaternion. -/
def quatInt : AddSubgroup ℍ[ℝ] :=
  AddSubgroup.closure {e₁, e₂, e₃, e₄}

/-- Hurwitz quaternion. -/
def f4Lattice : AddSubgroup ℍ[ℝ] :=
  AddSubgroup.closure {s, e₂, e₃, e₄}

theorem mem_f4Lattice_iff (q : ℍ[ℝ]) : q ∈ f4Lattice ↔ q ∈ quatInt ∨ q + s ∈ quatInt := by
  constructor
  intro h
  left
  intro q hq
  obtain ⟨n, rfl⟩ := hq
  apply set.mem_Inter.mpr fun hn => _
  apply hn
  simp
  right
  sorry
  sorry

-- { intro h,
--   have : q ∈ add_subgroup.closure {s, e₂, e₃, e₄} := h,
--   rw add_subgroup.mem_closure_iff at this,
--   rcases this with ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩,
--   suffices : a • s + b • e₂ + c • e₃ + d • e₄ ∈ quat_int,
--   { simpa, },
--   rw add_subgroup.mem_closure_iff,
--   refine ⟨a, b, c, d, ha, hb, hc, hd, _⟩,
-- }
/- Remarkable fact: this lattice is actually a subring. May or may not be useful.

def f4_order : subring ℍ[ℝ] :=
{ one_mem' := sorry,
  mul_mem' := sorry,
  .. f4_lattice }
-/
def f4RootSystem : Set ℍ[ℝ] :=
  {q : ℍ[ℝ] | ‖q‖ ^ 2 ≤ 2 ∧ q ∈ f4Lattice}

theorem isRootSystemF4RootSystem : IsRootSystem ℝ f4RootSystem :=
  { Finite := by
      constructor
      sorry
    span_eq_top := by sorry
    exists_dual := by
      intro α hα
      have : ‖α‖ * ‖α‖ ≠ 0 := by sorry
      let α' := (2 / (‖α‖ * ‖α‖)) • α
      refine' ⟨(InnerProductSpace.toDualMap ℝ ℍ[ℝ] α').toLinearMap, _, _⟩
      ·
        simp only [ContinuousLinearMap.toLinearMap_eq_coe, ContinuousLinearMap.coe_coe,
          InnerProductSpace.toDualMap_apply, inner_smul_left, IsROrC.conj_to_real,
          Quaternion.inner_self, Quaternion.normSq_eq_norm_mul_self, div_mul_cancel _ this]
      · rintro - ⟨β, hβ, rfl⟩
        suffices β - (2 / (‖α‖ * ‖α‖) * inner α β) • α ∈ f4RootSystem by simpa
        -- There are only finitely-many (in fact 48) possible `α` and `β`. We could therefore
        -- use a mathematically low-tech but computer-sciencey high-tech proof that brute forces
        -- all cases to generate a proof, using some Lean meta code.
        sorry
    subset_zmultiples := by
      rintro α hα f ⟨hf, hf'⟩ - ⟨β, hβ, rfl⟩
      -- Likewise actually a finite calculation.
      sorry }
