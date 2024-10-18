import Mathlib.Analysis.Normed.Field.Basic

variable {α : Type*} [NonUnitalSeminormedRing α] {a a₁ a₂ b c : α} {r₁ r₂ : ℝ}

-- TODO: Rename unprimed versions
lemma norm_mul_le_of_le' (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ * r₂ :=
  (norm_mul_le a₁ a₂).trans <| mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le' (norm_mul_le ..) le_rfl
