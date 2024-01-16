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
