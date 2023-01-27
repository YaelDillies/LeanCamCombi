import logic.relation

variables {α β γ δ ε ν : Type*}

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

end relation
