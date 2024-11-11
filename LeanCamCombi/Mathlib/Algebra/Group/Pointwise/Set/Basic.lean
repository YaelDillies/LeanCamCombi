import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise

namespace Set
variable {α : Type*}

section Monoid
variable [Monoid α] {s t : Set α} {n : ℕ}

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
    · exact hs.pow
    · simp
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
variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

@[to_additive]
lemma Nonempty.zpow (hs : s.Nonempty) : ∀ {n : ℤ}, (s ^ n).Nonempty
  | (n : ℕ) => hs.pow
  | .negSucc n => by simpa using hs.pow

set_option push_neg.use_distrib true in
@[to_additive (attr := simp)] lemma zpow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose!
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

end DivisionMonoid
end Set

namespace Set
variable {ι : Type*} {α : ι → Type*} [∀ i, InvolutiveInv (α i)]

@[to_additive (attr := simp)]
lemma inv_pi (s : Set ι) (t : ∀ i, Set (α i)) : (s.pi t)⁻¹ = s.pi fun i ↦ (t i)⁻¹ := by
  simp_rw [← image_inv]; exact piMap_image_pi (fun _ _ ↦ inv_surjective) _

end Set

variable {α} [Monoid α] {s : Set α}

lemma pow_right_mono (hs : 1 ∈ s) : Monotone (s ^ ·) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [pow_succ]
  exact subset_mul_left _ hs

@[gcongr]
lemma GCongr.pow_right_mono (hs : 1 ∈ s) {m n : ℕ} (hmn : m ≤ n) : s ^ m ⊆ s ^ n :=
  Set.pow_right_mono hs hmn

@[gcongr]
lemma pow_left_mono {s t : Set α} (hst : s ⊆ t) : ∀ {n : ℕ}, s ^ n ⊆ t ^ n
  | 0 => by simp
  | n + 1 => by simp_rw [pow_succ]; gcongr; exact pow_left_mono hst

@[gcongr]
lemma pow_mono {s t : Set α} (hst : s ⊆ t) (ht : 1 ∈ t) {m n : ℕ} (hmn : m ≤ n) :
    s ^ m ⊆ t ^ n :=
  (pow_left_mono hst).trans (pow_right_mono ht hmn)

end Set
