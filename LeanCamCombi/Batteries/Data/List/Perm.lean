import Batteries.Data.List.Perm

attribute [simp] List.nil_subperm

namespace List
variable {α : Type _} {l l' l₀ l₁ l₂ : List α} {a b : α}

theorem subperm_cons_self : l <+~ a :: l := ⟨l, Perm.refl _, sublist_cons_self _ _⟩

@[simp] theorem subperm_nil : l <+~ [] ↔ l = [] :=
  ⟨fun h ↦ length_eq_zero.1 $ Nat.le_zero.1 h.length_le, by rintro rfl; rfl⟩

end List
