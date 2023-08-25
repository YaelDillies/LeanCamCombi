import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Powerset
import Mathbin.Data.Finset.Sups

#align_import four_functions

/-!
# The four functions theorem and FKG inequality

-/


open scoped BigOperators FinsetFamily

variable {α β : Type _}

section Lattice

variable [Lattice α] [Mul β] [LE β]

/-- Four functions `f₁`, `f₂`, `f₃`, `f₄` are log-super modular if -/
def LogSuperModular (f₁ f₂ f₃ f₄ : α → β) : Prop :=
  ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b)

end Lattice

protected theorem LinearOrder.logSuperModular [LinearOrder α] [CommSemigroup β] [Preorder β]
    (f : α → β) : LogSuperModular f f f f := fun a b => by cases le_total a b <;> simp [h, mul_comm]

section Finset

variable [DecidableEq α] [OrderedSemiring β] {f f₁ f₂ f₃ f₄ g μ : Finset α → β}

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s «expr ⊆ » u) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s «expr ⊆ » u) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s «expr ⊆ » u) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s «expr ⊆ » u) -/
/-- The **four functions theorem** -/
theorem four_functions_theorem' {u : Finset α} (h₁ : ∀ (s) (_ : s ⊆ u), 0 ≤ f₁ s)
    (h₂ : ∀ (s) (_ : s ⊆ u), 0 ≤ f₂ s) (h₃ : ∀ (s) (_ : s ⊆ u), 0 ≤ f₃ s)
    (h₄ : ∀ (s) (_ : s ⊆ u), 0 ≤ f₄ s) (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b))
    {s t : Finset (Finset α)} (hs : s ⊆ u.powerset) (ht : t ⊆ u.powerset) :
    (∑ a in s, f₁ a) * ∑ b in t, f₂ b ≤ (∑ a in s ⊻ t, f₃ a) * ∑ b in s ⊼ t, f₄ b :=
  by
  induction' u using Finset.induction with a u h ih generalizing f₁ f₂ f₃ f₄
  · simp only [Finset.powerset_empty, Finset.subset_singleton_iff] at hs ht 
    obtain rfl | rfl := hs <;> obtain rfl | rfl := ht <;>
      first
      | simpa using h ∅ ∅
      | simp
  sorry

end Finset

variable [DistribLattice α] [DecidableEq α] [OrderedSemiring β] {f f₁ f₂ f₃ f₄ g μ : α → β}

/-- The **four functions theorem** -/
theorem four_functions_theorem {s t u : Finset α} (h₁ : ∀ a ∈ u, 0 ≤ f₁ a) (h₂ : ∀ a ∈ u, 0 ≤ f₂)
    (h₃ : ∀ a ∈ u, 0 ≤ f₃) (h₄ : ∀ a ∈ u, 0 ≤ f₄) (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b))
    (hs : s ⊆ u) (ht : t ⊆ u) :
    (∑ a in s, f₁ a) * ∑ b in t, f₂ b ≤ (∑ a in s ∪ t, f₃ a) * ∑ b in s ∩ t, f₄ b := by sorry

theorem fkg [Fintype α] (hμ : 0 ≤ μ) (hf : Monotone f) (hg : Monotone g) :
    (∑ a, f a * μ a) * ∑ a, g a * μ a ≤ (∑ a, f a * g a * μ a) * ∑ a, μ a := by sorry

