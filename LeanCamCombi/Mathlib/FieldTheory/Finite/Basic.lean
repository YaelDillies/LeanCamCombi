import Mathlib.FieldTheory.Finite.Basic

namespace ZMod
variable {p : ℕ} [Fact p.Prime]

lemma pow_card_sub_one (x : ZMod p) : x ^ (p - 1) = if x ≠ 0 then 1 else 0 := by
  split_ifs with hx
  · exact pow_card_sub_one_eq_one hx
  · simp [of_not_not hx, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]

end ZMod
