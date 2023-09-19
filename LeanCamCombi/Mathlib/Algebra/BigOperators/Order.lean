import Mathlib.Algebra.BigOperators.Order

variable {α β : Type*}

open scoped BigOperators

namespace Fintype
variable [Fintype α] [StrictOrderedSemiring β] {f : α → β}

lemma sum_nonneg (hf : 0 ≤ f) : 0 ≤ ∑ a, f a := Finset.sum_nonneg λ _ _ ↦ hf _

lemma sum_pos (hf : 0 < f) : 0 < ∑ a, f a :=
  Finset.sum_pos' (λ _ _ ↦ hf.le _) $ by simpa using (Pi.lt_def.1 hf).2

lemma sum_pos_iff_of_nonneg (hf : 0 ≤ f) : 0 < ∑ a, f a ↔ 0 < f := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, sum_pos]

lemma sum_eq_zero_iff_of_nonneg (hf : 0 ≤ f) : ∑ a, f a = 0 ↔ f = 0 := by
  simpa only [(sum_nonneg hf).not_gt_iff_eq, hf.not_gt_iff_eq] using (sum_pos_iff_of_nonneg hf).not

end Fintype
