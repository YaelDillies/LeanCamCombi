import logic.basic

variables {α β : Type*} {a b : α} {c d : β}

protected lemma iff.ne : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) := iff.not
