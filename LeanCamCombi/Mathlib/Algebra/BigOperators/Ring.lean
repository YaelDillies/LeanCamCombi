import Mathlib.Algebra.BigOperators.Ring

open scoped BigOperators

namespace Finset
variable {ι α : Type*}

section NonAssocSemiring
variable [NonAssocSemiring α] [DecidableEq ι]

-- TODO: Replace `sum_boole_mul`
lemma sum_boole_mul' (s : Finset ι) (f : ι → α) (i : ι) :
    ∑ j in s, ite (i = j) 1 0 * f j = ite (i ∈ s) (f i) 0 := by simp

end NonAssocSemiring
end Finset

open Finset

namespace Int
variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [Int.ediv_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [Int.ediv_mul_cancel (hf _ hs)]

end Int
