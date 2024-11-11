import Mathlib
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace Submodule

open scoped Pointwise

variable {R : Type*} {M : Type*}

variable [CommSemiring R] [Semiring M] [Algebra R M]

variable {s t : Submodule R M}

lemma pow_right_mono (hs : 1 ≤ s) : Monotone (s ^ ·) := fun _ _ e ↦ pow_le_pow_right' hs e

@[gcongr]
lemma GCongr.pow_right_mono (hs : 1 ≤ s) {m n : ℕ} (hmn : m ≤ n) : s ^ m ≤ s ^ n :=
  Submodule.pow_right_mono hs hmn

@[gcongr]
lemma pow_left_mono (hst : s ≤ t) : ∀ {n : ℕ}, s ^ n ≤ t ^ n := by exact fun {n} ↦ pow_le_pow_left' hst n

@[gcongr]
lemma pow_mono (hst : s ≤ t) (ht : 1 ≤ t) {m n : ℕ} (hmn : m ≤ n) :
    s ^ m ≤ t ^ n :=
  (pow_le_pow_left' hst _).trans (pow_le_pow_right' ht hmn)

end Submodule
