theorem Function.comp_def {α β δ : Sort _} (f : β → δ) (g : α → β) :
    f ∘ g = fun x ↦ f (g x) := rfl
