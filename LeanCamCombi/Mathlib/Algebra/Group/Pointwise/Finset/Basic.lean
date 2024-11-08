import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α] [Mul α] {s t : Finset α} {a : α}

lemma smul_finset_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image₂_right

attribute [gcongr] mul_subset_mul_left mul_subset_mul_right div_subset_div_left div_subset_div_right

end Finset

namespace Finset
variable {α : Type*} [DecidableEq α]

section Monoid
variable [Monoid α] {s t : Finset α} {n : ℕ}

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
end Finset
