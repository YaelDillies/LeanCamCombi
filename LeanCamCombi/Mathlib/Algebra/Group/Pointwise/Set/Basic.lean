import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise

namespace Set
variable {F α β : Type*}

section Monoid
variable [Monoid α] [Monoid β] {s t : Set α} {n : ℕ}

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
lemma pow_left_mono : Monotone fun s : Set α ↦ s ^ n := fun _s _t hst ↦  pow_subset_pow_left hst

@[to_additive (attr := gcongr)]
lemma pow_subset_pow' (hst : s ⊆ t) (ht : 1 ∈ t) {m n : ℕ} (hmn : m ≤ n) : s ^ m ⊆ t ^ n :=
  (pow_left_mono hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]
lemma image_pow [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Set α) :
    ∀ n, f '' (s ^ n) = (f '' s) ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by simp [image_mul, pow_succ, image_pow]

@[to_additive]
lemma one_mem_pow (hs : 1 ∈ s) : ∀ {n}, 1 ∈ s ^ n
  | 0 => by simp
  | n + 1 => by simpa [pow_succ] using mul_mem_mul (one_mem_pow hs) hs

@[to_additive]
lemma inter_pow_subset : (s ∩ t) ^ n ⊆ s ^ n ∩ t ^ n := by apply subset_inter <;> gcongr <;> simp

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

section Group
variable [Group α] {s t : Set α} {a b : α}

@[to_additive (attr := simp)]
lemma one_mem_inv_mul_iff : (1 : α) ∈ t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv, Set.Nonempty])

@[to_additive]
lemma not_one_mem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := one_mem_inv_mul_iff.not_left

@[to_additive]
lemma image_inv' [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Set α) :
    f '' s⁻¹ = (f '' s)⁻¹ := by rw [← image_inv, ← image_inv]; exact image_comm (map_inv _)

end Group
end Set

namespace Set
variable {ι : Type*} {α : ι → Type*} [∀ i, InvolutiveInv (α i)]

@[to_additive (attr := simp)]
lemma inv_pi (s : Set ι) (t : ∀ i, Set (α i)) : (s.pi t)⁻¹ = s.pi fun i ↦ (t i)⁻¹ := by
  simp_rw [← image_inv]; exact piMap_image_pi (fun _ _ ↦ inv_surjective) _
end Set
