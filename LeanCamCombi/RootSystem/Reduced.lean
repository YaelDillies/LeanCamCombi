import LeanCamCombi.RootSystem.Basic

open Set Function

/-- A reduced, crystallographic root system. -/
structure IsReducedRootSystem (k : Type _) {V : Type _} [CommRing k] [CharZero k] [AddCommGroup V]
    [Module k V] (Φ : Set V) extends IsRootSystem k Φ : Prop where
  two_smul_not_mem : ∀ α ∈ Φ, 2 • α ∉ Φ

namespace IsRootSystem

variable {k V : Type _} [Field k] [CharZero k] [AddCommGroup V] [Module k V]

variable {Φ : Set V} (h : IsRootSystem k Φ)

local postfix:100 "ᘁ" => h.coroot

local notation "ട" => h.symmetryOfRoot

theorem foo {k : Type _} {V : Type _} (n m : ℤ) [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    {Φ : Set V} (hr : IsReducedRootSystem k Φ) (x : V) (hx : x ∈ Φ) (t : k) (ht : t • x ∈ Φ)
    (ht₀ : t ≠ 0) (htn : t * ↑n = 2) (htm : t⁻¹ * ↑m = 2) (hmn : n * m = 4) (hn : n ≠ 1)
    (hn' : n ≠ -1) :
    let α : ↥Φ := ⟨x, hx⟩
    let β : ↥Φ := ⟨t • x, ht⟩
    t⁻¹ • (β : V) = α → (hr.coroot β) ↑α = ↑n → (hr.coroot α) ↑β = ↑m → m ≠ 1 := by
  intro α β hαβ hn_1 hm
  have := hr.two_smul_not_mem β β.property
  contrapose! this
  sorry

-- rw [this, algebra_map.coe_one, mul_one, inv_eq_iff_inv_eq] at htm,
-- simpa only [nsmul_eq_smul_cast k 2, nat.cast_two, subtype.coe_mk, smul_inv_smul₀, ne.def,
--               bit0_eq_zero, one_ne_zero, not_false_iff, ← htm],
theorem m_not_neg_1 {k : Type _} {V : Type _} (n m : ℤ) [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] {Φ : Set V} (h : IsRootSystem k Φ) (hr : IsReducedRootSystem k Φ) (x : V)
    (hx : x ∈ Φ) (t : k) (ht : t • x ∈ Φ) (ht₀ : t ≠ 0) (htn : t * ↑n = 2) (htm : t⁻¹ * ↑m = 2)
    (hmn : n * m = 4) (hn : n ≠ 1) (hn' : n ≠ -1) :
    let α : ↥Φ := ⟨x, hx⟩
    let β : ↥Φ := ⟨t • x, ht⟩
    t⁻¹ • (β : V) = α → (h.coroot β) ↑α = ↑n → (h.coroot α) ↑β = ↑m → m ≠ -1 := by
  intro α β hαβ hn_1 hm
  have := hr.two_smul_not_mem (-β) (h.neg_mem β)
  contrapose! this
  simp only [nsmul_eq_smul_cast k 2, Nat.cast_two, Subtype.coe_mk, smul_neg]
  sorry

-- rw [this, int.cast_neg, algebra_map.coe_one, mul_neg, mul_one, neg_eq_iff_neg_eq, eq_inv_iff_eq_inv] at htm,
-- rw htm,
-- simpa [← neg_inv],
theorem is_reduced_iff (h : IsRootSystem k Φ) :
    IsReducedRootSystem k Φ ↔ ∀ α ∈ Φ, ∀ (t : k), t • α ∈ Φ → t = 1 ∨ t = -1 := by
  refine' ⟨fun hr x hx t ht => _, fun hr => ⟨h, fun α hα contra => _⟩⟩
  · let α : Φ := ⟨x, hx⟩
    let β : Φ := ⟨t • x, ht⟩
    have ht₀ : t ≠ 0 := by have := h.zero_not_mem; contrapose! this; rwa [this, zero_smul] at ht
    have hαβ : t⁻¹ • (β : V) = α := by
      rw [Subtype.coe_mk, Subtype.coe_mk, smul_smul, inv_mul_cancel ht₀, one_smul]
    obtain ⟨n, hn⟩ := h.exists_int_coroot_apply_eq β α
    have htn : t * n = 2 := by
      have : (βᘁ) (t • α) = 2 := h.coroot_apply_self_eq_two β
      simpa only [LinearMap.map_smulₛₗ, RingHom.id_apply, Algebra.id.smul_eq_mul, hn] using this
    obtain ⟨m, hm⟩ := h.exists_int_coroot_apply_eq α β
    have htm : t⁻¹ * m = 2 := by
      have : (αᘁ) (t⁻¹ • β) = 2 := by rw [hαβ]; exact h.coroot_apply_self_eq_two α
      simpa only [LinearMap.map_smulₛₗ, RingHom.id_apply, Algebra.id.smul_eq_mul, hm] using this
    have hmn : n * m = 4 := by
      have := congr_arg₂ ((· * ·) : k → k → k) htn htm
      rw [mul_mul_mul_comm, mul_inv_cancel ht₀, one_mul] at this
      norm_cast at this
      exact this
    have hn1 : n ≠ 1 := by
      have := hr.two_smul_not_mem α α.property
      contrapose! this
      simp only [nsmul_eq_smul_cast k 2, Nat.cast_two, Subtype.coe_mk]
      rw [this, algebraMap.coe_one, mul_one] at htn
      rwa [htn] at ht
    have hnm1 : n ≠ -1 := by
      have := hr.two_smul_not_mem (-α) (h.neg_mem α)
      contrapose! this
      simp only [nsmul_eq_smul_cast k 2, Nat.cast_two, Subtype.coe_mk, smul_neg]
      rw [this, Int.cast_neg, algebraMap.coe_one, mul_neg, mul_one, neg_eq_iff_eq_neg] at htn
      sorry
    -- rwa [← htn, neg_smul] at ht,
    -- Similarly `m ≠ ± 1`. Using `hmn : n * m = 4` this means `n`, `m` both `± 2`, thus `t = ± 1`.
    have hm1 : m ≠ 1 := foo n m hr x hx t ht ht₀ htn htm hmn hn1 hnm1 hαβ hn hm
    have hmn1 : m ≠ -1 := m_not_neg_1 n m h hr x hx t ht ht₀ htn htm hmn hn1 hnm1 hαβ hn hm
    suffices n = 2 ∨ n = -2 by
      rcases this with (rfl | rfl)
      · left
        rwa [Int.cast_two, ← eq_mul_inv_iff_mul_eq₀ (NeZero.ne (2 : k)),
          mul_inv_cancel (NeZero.ne (2 : k))] at htn
      · right
        sorry
    -- rwa [int.cast_neg, int.cast_two, mul_neg, neg_eq_iff_eq_neg,
    -- ← mul_inv_eq_iff_eq_mul₀ (ne_zero.ne (2 : k)), neg_mul,
    -- mul_inv_cancel (ne_zero.ne (2 : k)), eq_comm] at htn,
    suffices n.nat_abs = 2 by
      cases' n.nat_abs_eq with h h
      · left; rw [h, this, Nat.cast_two]
      · right; rw [h, this, Nat.cast_two]
    have hn4 : n ≠ 4 := by
      contrapose! hmn1
      simpa [hmn1, mul_right_eq_self₀] using hmn
    have hnm4 : n ≠ -4 := by
      contrapose! hmn1
      refine' neg_eq_iff_eq_neg.1 _
      simpa [hmn1, mul_right_eq_self₀, ← mul_neg] using hmn
    replace hmn := congr_arg Int.natAbs hmn
    rw [Int.natAbs_mul, (by norm_num : (4 : ℤ).natAbs = 4)] at hmn
    replace hmn : n.nat_abs ∣ 4 := ⟨m.nat_abs, hmn.symm⟩
    rcases Nat.eq_one_or_two_or_four_of_div_four hmn with (h | h | h)
    · exfalso
      cases Int.natAbs_eq n
      · rw [h, Nat.cast_one] at h_1
        exact hn1 h_1
      · rw [h, Nat.cast_one] at h_1
        contradiction
    · assumption
    · cases Int.natAbs_eq n
      exfalso
      · rw [h] at h_1
        norm_cast at h_1
      · rw [h] at h_1
        norm_cast at h_1
  · replace contra : (2 : k) • α ∈ Φ; · rwa [nsmul_eq_smul_cast k 2 α, Nat.cast_two] at contra
    have h2 := hr α hα (2 : k) contra
    norm_num at h2

end IsRootSystem
