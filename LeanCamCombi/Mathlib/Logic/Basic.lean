import Mathlib.Logic.Basic

variable {α β : Type*} {a b : α} {c d : β}

protected lemma Iff.ne : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) :=
  Iff.not
