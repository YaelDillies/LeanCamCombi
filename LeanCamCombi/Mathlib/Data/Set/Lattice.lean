import Mathlib.Data.Set.Lattice

namespace Set
variable {α β γ δ : Type*}

lemma biUnion_image2 (s : Set α) (t : Set β) (f : α → β → γ) (g : γ → Set δ) :
    ⋃ c ∈ image2 f s t, g c = ⋃ a ∈ s, ⋃ b ∈ t, g (f a b) := iSup_image2 ..

lemma biInter_image2 (s : Set α) (t : Set β) (f : α → β → γ) (g : γ → Set δ) :
    ⋂ c ∈ image2 f s t, g c = ⋂ a ∈ s, ⋂ b ∈ t, g (f a b) := iInf_image2 ..

lemma iUnion_inter_iUnion {ι κ : Sort*} (f : ι → Set α) (g : κ → Set α) :
    (⋃ i, f i) ∩ ⋃ j, g j = ⋃ i, ⋃ j, f i ∩ g j := by simp_rw [iUnion_inter, inter_iUnion]

lemma iInter_union_iInter {ι κ : Sort*} (f : ι → Set α) (g : κ → Set α) :
    (⋂ i, f i) ∪ ⋂ j, g j = ⋂ i, ⋂ j, f i ∪ g j := by simp_rw [iInter_union, union_iInter]

lemma iUnion₂_inter_iUnion₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ → Sort*} {k₂ : κ₁ → Sort*}
    (f : ∀ i₁, ι₂ i₁ → Set α) (g : ∀ j₁, k₂ j₁ → Set α) :
    (⋃ i₁, ⋃ i₂, f i₁ i₂) ∩ ⋃ j₁, ⋃ j₂, g j₁ j₂ = ⋃ i₁, ⋃ i₂, ⋃ j₁, ⋃ j₂, f i₁ i₂ ∩ g j₁ j₂ := by
  simp_rw [iUnion_inter, inter_iUnion]

lemma iInter₂_union_iInter₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ → Sort*} {k₂ : κ₁ → Sort*}
    (f : ∀ i₁, ι₂ i₁ → Set α) (g : ∀ j₁, k₂ j₁ → Set α) :
    (⋂ i₁, ⋂ i₂, f i₁ i₂) ∪ ⋂ j₁, ⋂ j₂, g j₁ j₂ = ⋂ i₁, ⋂ i₂, ⋂ j₁, ⋂ j₂, f i₁ i₂ ∪ g j₁ j₂ := by
  simp_rw [iInter_union, union_iInter]

end Set
