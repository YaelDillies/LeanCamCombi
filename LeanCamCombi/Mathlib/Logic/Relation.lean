import Mathlib.Logic.Relation

open Function

variable {α β γ δ ε ν : Type _} {f : α → γ} {g : β → δ}

namespace Relation

@[simp]
lemma map_id_id (r : α → β → Prop) : Relation.Map r id id = r := by simp [Relation.Map]

@[simp]
lemma map_map (r : α → β → Prop) (f₁ : α → γ) (g₁ : β → δ) (f₂ : γ → ε) (g₂ : δ → ν) :
    Relation.Map (Relation.Map r f₁ g₁) f₂ g₂ = Relation.Map r (f₂ ∘ f₁) (g₂ ∘ g₁) := by
  ext a b
  simp_rw [Relation.Map, Function.comp_apply, ←exists_and_right, @exists_comm γ, @exists_comm δ]
  refine' exists₂_congr fun a b ↦ ⟨_, fun h ↦ ⟨_, _, ⟨⟨h.1, rfl, rfl⟩, h.2⟩⟩⟩
  rintro ⟨_, _, ⟨hab, rfl, rfl⟩, h⟩
  exact ⟨hab, h⟩

@[simp]
lemma map_apply_apply (hf : Injective f) (hg : Injective g) (r : α → β → Prop) (a : α) (b : β) :
    Relation.Map r f g (f a) (g b) ↔ r a b := by simp [Relation.Map, hf.eq_iff, hg.eq_iff]

end Relation
