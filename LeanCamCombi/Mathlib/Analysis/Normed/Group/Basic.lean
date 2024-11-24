import Mathlib.Analysis.Normed.Group.Basic

variable {E : Type} [SeminormedGroup E]

@[to_additive norm_nsmul_le']
theorem norm_pow_le_mul_norm' (n : ℕ) (a : E) : ‖a ^ n‖ ≤ n * ‖a‖ := by
  induction' n with n ih; · simp
  simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using norm_mul_le_of_le' ih le_rfl

@[to_additive nnnorm_nsmul_le']
theorem nnnorm_pow_le_mul_norm' (n : ℕ) (a : E) : ‖a ^ n‖₊ ≤ n * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using
    norm_pow_le_mul_norm' n a
