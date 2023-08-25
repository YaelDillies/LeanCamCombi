import Mathbin.Logic.Basic

#align_import mathlib.logic.basic

variable {α β : Type _} {a b : α} {c d : β}

protected theorem Iff.ne : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) :=
  Iff.not

