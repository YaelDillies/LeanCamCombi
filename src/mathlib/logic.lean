import logic.lemmas
import tactic

lemma Prop.forall_iff {f : Prop → Prop} : (∀ p, f p) ↔ f true ∧ f false :=
⟨λ h, ⟨h _, h _⟩, by { rintro ⟨h₁, h₀⟩ p, by_cases hp : p; simp only [hp]; assumption }⟩
