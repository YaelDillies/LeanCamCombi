import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α] [Mul α] {s t : Finset α} {a : α}

lemma smul_finset_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image₂_right

attribute [gcongr] mul_subset_mul_left mul_subset_mul_right div_subset_div_left div_subset_div_right

end Finset

namespace Finset
variable {F α β : Type*} [DecidableEq α] [DecidableEq β]

section Monoid
variable [Monoid α] [Monoid β] {s t : Finset α} {n : ℕ}

attribute [simp] one_nonempty

@[to_additive]
lemma Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs

set_option push_neg.use_distrib true in
@[to_additive (attr := simp)] lemma pow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose!
    rintro (hs | rfl)
    -- TODO: The `nonempty_iff_ne_empty` would be unnecessary if `push_neg` knew how to simplify
    -- `s ≠ ∅` to `s.Nonempty` when `s : Finset α`.
    -- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/push_neg.20extensibility
    · exact nonempty_iff_ne_empty.1 (nonempty_iff_ne_empty.2 hs).pow
    · rw [← nonempty_iff_ne_empty]
      simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive]
lemma pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 ⊆ t * s) :
    ∀ {n}, 1 < n → s ^ n ⊆ t ^ (n - 1) * s
  | 2, _ => by simpa
  | n + 3, _ => by
    calc
      s ^ (n + 3) = s ^ (n + 2) * s := by rw [pow_succ]
      _ ⊆ t ^ (n + 1) * s * s := by gcongr; exact pow_subset_pow_mul_of_sq_subset_mul hst (by omega)
      _ = t ^ (n + 1) * s ^ 2 := by rw [mul_assoc, sq]
      _ ⊆ t ^ (n + 1) * (t * s) := by gcongr
      _ = t ^ (n + 2) * s := by rw [← mul_assoc, ← pow_succ]

@[to_additive]
lemma pow_right_mono (hs : 1 ∈ s) : Monotone (s ^ ·) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [pow_succ]
  exact subset_mul_left _ hs

@[to_additive (attr := gcongr)]
lemma pow_subset_pow_right (hs : 1 ∈ s) {m n : ℕ} (hmn : m ≤ n) : s ^ m ⊆ s ^ n :=
  pow_right_mono hs hmn

-- TODO: Replace `pow_subset_pow`
@[to_additive (attr := gcongr)]
lemma pow_subset_pow_left (hst : s ⊆ t) : ∀ {n : ℕ}, s ^ n ⊆ t ^ n
  | 0 => by simp
  | n + 1 => by simp_rw [pow_succ]; gcongr; exact pow_subset_pow_left hst

@[to_additive]
lemma pow_left_mono : Monotone fun s : Finset α ↦ s ^ n := fun _s _t hst ↦ pow_subset_pow_left hst

-- TODO: Replace `pow_subset_pow`
@[to_additive (attr := gcongr)]
lemma pow_subset_pow' (hst : s ⊆ t) (ht : 1 ∈ t) {m n : ℕ} (hmn : m ≤ n) : s ^ m ⊆ t ^ n :=
  (pow_left_mono hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]
lemma image_pow [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Finset α) :
    ∀ n, (s ^ n).image f = s.image f ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by simp [image_mul, pow_succ, image_pow]

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

@[to_additive]
lemma Nonempty.zpow (hs : s.Nonempty) : ∀ {n : ℤ}, (s ^ n).Nonempty
  | (n : ℕ) => hs.pow
  | .negSucc n => by simpa using hs.pow

set_option push_neg.use_distrib true in
@[to_additive (attr := simp)] lemma zpow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose!
    rintro (hs | rfl)
    · exact nonempty_iff_ne_empty.1 (nonempty_iff_ne_empty.2 hs).zpow
    · rw [← nonempty_iff_ne_empty]
      simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

end DivisionMonoid

section Group
variable [Group α] {s t : Finset α}

@[to_additive (attr := simp)]
lemma one_mem_inv_mul_iff : (1 : α) ∈ t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv,
    Finset.Nonempty])

@[to_additive]
lemma not_one_mem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := one_mem_inv_mul_iff.not_left

end Group
end Finset
