import Mathlib.Analysis.Normed.Group.Basic

open scoped NNReal

section ContinuousInv
variable {α E : Type*} [SeminormedCommGroup E] [PseudoEMetricSpace α] {K : ℝ≥0}
  {f : α → E} {s : Set α} {x : α}

@[to_additive (attr := simp)]
lemma lipschitzWith_inv_iff : LipschitzWith K f⁻¹ ↔ LipschitzWith K f := by simp [LipschitzWith]

@[to_additive (attr := simp)]
lemma lipschitzOnWith_inv_iff : LipschitzOnWith K f⁻¹ s ↔ LipschitzOnWith K f s := by
  simp [LipschitzOnWith]

@[to_additive (attr := simp)]
lemma locallyLipschitz_inv_iff : LocallyLipschitz f⁻¹ ↔ LocallyLipschitz f := by
  simp [LocallyLipschitz]

@[to_additive (attr := simp)]
lemma antilipschitzWith_inv_iff : AntilipschitzWith K f⁻¹ ↔ AntilipschitzWith K f := by
  simp [AntilipschitzWith]

end ContinuousInv
