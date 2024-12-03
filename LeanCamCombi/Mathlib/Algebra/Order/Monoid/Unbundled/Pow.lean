import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

variable {M : Type*} [Monoid M] [Preorder M] {a : M} {n : ℕ} [MulLeftMono M]

-- TODO: Replace `le_self_pow`
@[to_additive le_nsmul_self]
lemma le_self_pow' (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa using pow_le_pow_right' ha (Nat.one_le_iff_ne_zero.2 hn)

