import Mathlib.Data.Finsupp.Order

namespace Finsupp

lemma support_monotone {α M} [CanonicallyOrderedAddMonoid M] :
    Monotone (support (α := α) (M := M)) :=
  λ f g h a ha ↦ by rw [mem_support_iff, ←pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)

end Finsupp
