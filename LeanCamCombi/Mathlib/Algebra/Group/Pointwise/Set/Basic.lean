import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise

namespace Set
variable {α : Type*} [Monoid α] {s t : Set α}

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

end Set

namespace Set
variable {ι : Type*} {α : ι → Type*} [∀ i, InvolutiveInv (α i)]

@[to_additive (attr := simp)]
lemma inv_pi (s : Set ι) (t : ∀ i, Set (α i)) : (s.pi t)⁻¹ = s.pi fun i ↦ (t i)⁻¹ := by
  simp_rw [← image_inv]; exact piMap_image_pi (fun _ _ ↦ inv_surjective) _

end Set
