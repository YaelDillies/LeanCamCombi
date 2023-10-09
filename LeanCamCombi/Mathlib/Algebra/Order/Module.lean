import Mathlib.Algebra.Order.Module


section
variable {ι α β : Type*} [LinearOrderedRing α] [LinearOrderedAddCommGroup β] [Module α β]
  [OrderedSMul α β] {f : ι → α} {g : ι → β} {s : Set ι} {a a₁ a₂ : α} {b b₁ b₂ : β}

-- TODO: Rename `nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg` to
-- `nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg`
lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 ≤ a • b) :
    0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp only [Decidable.or_iff_not_and_not, not_and, not_le]
  refine fun ab nab ↦ hab.not_lt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]

lemma smul_nonneg_iff : 0 ≤ a • b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h ↦ h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

lemma smul_nonpos_iff : a • b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [←neg_nonneg, ←smul_neg, smul_nonneg_iff, neg_nonneg, neg_nonpos]

lemma smul_nonneg_iff_pos_imp_nonneg : 0 ≤ a • b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine smul_nonneg_iff.trans ?_
  simp_rw [←not_le, ←or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

lemma smul_nonneg_iff_neg_imp_nonpos : 0 ≤ a • b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [←neg_smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_pos_imp_nonpos : a • b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [←neg_nonneg, ←smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_neg_imp_nonneg : a • b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [←neg_nonneg, ←neg_smul, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end
