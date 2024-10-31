import Mathlib.RingTheory.Ideal.Span

variable {R : Type*} [Semiring R]

@[simp] lemma Ideal.span_singleton_zero : Ideal.span {0} = (⊥ : Ideal R) := by simp
