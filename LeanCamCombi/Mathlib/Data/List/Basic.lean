import Mathlib.Data.List.Basic

namespace List
variable {α : Type*} {l l' l₀ l₁ l₂ : List α} {a b : α} {m n : ℕ}

attribute [simp] nil_subperm

lemma subperm_cons_self : l <+~ a :: l := ⟨l, Perm.refl _, sublist_cons_self _ _⟩

@[simp] lemma subperm_nil : l <+~ [] ↔ l = [] :=
  ⟨fun h ↦ length_eq_zero.1 $ Nat.le_zero.1 h.length_le, by rintro rfl; rfl⟩

end List
