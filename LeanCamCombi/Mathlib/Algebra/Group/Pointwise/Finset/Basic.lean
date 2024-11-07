import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α] [Mul α] {s t : Finset α} {a : α}

lemma smul_finset_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image₂_right

attribute [gcongr] mul_subset_mul_left mul_subset_mul_right div_subset_div_left div_subset_div_right

end Finset

namespace Finset
variable {α : Type*} [DecidableEq α] [Monoid α] {s t : Finset α}

attribute [simp] one_nonempty

@[to_additive]
lemma Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs

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

end Finset
