import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

variable {M : Type*} [Monoid M]

section Preorder
variable [Preorder M] {a : M} {n : ℕ} [MulLeftMono M]

-- TODO: Replace `le_self_pow`
@[to_additive le_nsmul_self]
lemma le_self_pow' (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa using pow_le_pow_right' ha (Nat.one_le_iff_ne_zero.2 hn)

end Preorder

section SemilatticeSup
variable [SemilatticeSup M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

lemma le_pow_sup : a ^ n ⊔ b ^ n ≤ (a ⊔ b) ^ n :=
  sup_le (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _)

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

lemma pow_inf_le : (a ⊓ b) ^ n ≤ a ^ n ⊓ b ^ n :=
  le_inf (pow_le_pow_left' inf_le_left _) (pow_le_pow_left' inf_le_right _)

end SemilatticeInf
