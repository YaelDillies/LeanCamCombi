import Mathlib.Algebra.Algebra.Operations

open scoped Pointwise

namespace Submodule

variable {R : Type*} {M : Type*}

variable [CommSemiring R] [Semiring M] [Algebra R M]

variable {s t : Submodule R M}

lemma pow_right_mono (hs : 1 ≤ s) : Monotone (s ^ ·) := fun _ _ e ↦ pow_le_pow_right' hs e

@[gcongr]
lemma GCongr.pow_right_mono (hs : 1 ≤ s) {m n : ℕ} (hmn : m ≤ n) : s ^ m ≤ s ^ n :=
  Submodule.pow_right_mono hs hmn

@[gcongr]
lemma pow_left_mono (hst : s ≤ t) : ∀ {n : ℕ}, s ^ n ≤ t ^ n := fun {n} ↦ pow_le_pow_left' hst n

@[gcongr]
lemma pow_mono (hst : s ≤ t) (ht : 1 ≤ t) {m n : ℕ} (hmn : m ≤ n) : s ^ m ≤ t ^ n :=
  (pow_le_pow_left' hst _).trans (pow_le_pow_right' ht hmn)

end Submodule

namespace Submodule
variable {R S : Type*} [CommRing R] [CommRing S]

lemma exists_lift_localization {s : Set R} {D : ℕ} {c : R} {f : R →+* S} [Invertible (f c)]
    (x : S) (hx : x ∈ span ℤ ({1} ∪ ⅟(f c) • f '' s) ^ D) :
    ∃ y ∈ span ℤ ({c} ∪ s) ^ D, f y = x * f c ^ D := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp
  | add x₁ x₂ D hx₁ hx₂ ih₁ ih₂ =>
    obtain ⟨y₁, hy₁, hyx₁⟩ := ih₁
    obtain ⟨y₂, hy₂, hyx₂⟩ := ih₂
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    simp [add_mul, hyx₁, hyx₂]
  | mem_mul m hm D x hx ih =>
    obtain ⟨n, hn, hnm⟩ : f c * m ∈ (span ℤ ({c} ∪ s)).map f.toIntAlgHom.toLinearMap := by
      simpa [map_span, span_mul_span, Set.image_insert_eq, ← Set.image_smul, Set.image_image]
        using mul_mem_mul (mem_span_singleton_self (f c)) hm
    obtain ⟨y, hy, hyx⟩ := ih
    dsimp at hnm
    rw [pow_succ']
    exact ⟨n * y, mul_mem_mul hn hy, by simp [hnm, hyx]; ring⟩

end Submodule
