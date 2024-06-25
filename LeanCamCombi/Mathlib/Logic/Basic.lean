import Mathlib.Logic.Basic

universe u
variable {α β : Sort u} {e : β = α} {a : α} {b : β}

lemma heq_comm : HEq a b ↔ HEq b a := by constructor <;> rintro ⟨⟩ <;> rfl

lemma heq_of_eq_cast (e : β = α) : a = cast e b → HEq a b := by rintro rfl; simp

lemma eq_cast_iff_heq : a = cast e b ↔ HEq a b :=
  ⟨heq_of_eq_cast _, fun h ↦ by cases h; rfl⟩
