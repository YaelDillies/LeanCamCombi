import logic.relation

open function

variables {α β γ δ ε ν : Type*} {f : α → γ} {g : β → δ}

namespace relation

@[simp] lemma map_id_id (r : α → β → Prop) : relation.map r id id = r := by simp [relation.map]

@[simp] lemma map_map (r : α → β → Prop) (f₁ : α → γ) (g₁ : β → δ) (f₂ : γ → ε) (g₂ : δ → ν) :
  relation.map (relation.map r f₁ g₁) f₂ g₂ = relation.map r (f₂ ∘ f₁) (g₂ ∘ g₁) :=
begin
  ext a b,
  simp_rw [relation.map, function.comp_app, ←exists_and_distrib_right, @exists_comm γ,
    @exists_comm δ],
  refine exists₂_congr (λ a b, ⟨_, λ h, ⟨_, _, ⟨⟨h.1, rfl, rfl⟩, h.2⟩⟩⟩),
  rintro ⟨_, _, ⟨hab, rfl, rfl⟩, h⟩,
  exact ⟨hab, h⟩,
end

@[simp]
lemma map_apply_apply (hf : injective f) (hg : injective g) (r : α → β → Prop) (a : α) (b : β) :
  relation.map r f g (f a) (g b) ↔ r a b :=
by simp [relation.map, hf.eq_iff, hg.eq_iff]

end relation
