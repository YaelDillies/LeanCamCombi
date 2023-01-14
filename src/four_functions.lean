import algebra.big_operators.basic
import data.finset.powerset
import data.finset.sups

/-!
# The four functions theorem and FKG inequality

-/

open_locale big_operators finset_family

variables {α β : Type*}

section lattice
variables [lattice α] [has_mul β] [has_le β]

/-- Four functions `f₁`, `f₂`, `f₃`, `f₄` are log-super modular if -/
def log_super_modular (f₁ f₂ f₃ f₄ : α → β) : Prop := ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b)

end lattice

protected lemma linear_order.log_super_modular [linear_order α] [comm_semigroup β] [preorder β]
  (f : α → β) :
  log_super_modular f f f f :=
λ a b, by cases le_total a b; simp [h, mul_comm]

section finset
variables [decidable_eq α] [ordered_semiring β] {f f₁ f₂ f₃ f₄ g μ : finset α → β}

/-- The **four functions theorem** -/
lemma four_functions_theorem' {u : finset α}  (h₁ : ∀ s ⊆ u, 0 ≤ f₁ s) (h₂ : ∀ s ⊆ u, 0 ≤ f₂ s)
  (h₃ : ∀ s ⊆ u, 0 ≤ f₃ s) (h₄ : ∀ s ⊆ u, 0 ≤ f₄ s)
  (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b)) {s t : finset (finset α)}
  (hs : s ⊆ u.powerset) (ht : t ⊆ u.powerset) :
  (∑ a in s, f₁ a) * (∑ b in t, f₂ b) ≤ (∑ a in s ⊻ t, f₃ a) * (∑ b in s ⊼ t, f₄ b) :=
begin
  induction u using finset.induction with a u h ih generalizing f₁ f₂ f₃ f₄,
  { simp only [finset.powerset_empty, finset.subset_singleton_iff] at hs ht,
    obtain rfl | rfl := hs; obtain rfl | rfl := ht; simpa using h ∅ ∅ <|> simp },
  sorry


end

end finset

variables [distrib_lattice α] [decidable_eq α] [ordered_semiring β]
  {f f₁ f₂ f₃ f₄ g μ : α → β}

/-- The **four functions theorem** -/
lemma four_functions_theorem {s t u : finset α} (h₁ : ∀ a ∈ u, 0 ≤ f₁ a) (h₂ : ∀ a ∈ u,  0 ≤ f₂)
  (h₃ : ∀ a ∈ u, 0 ≤ f₃) (h₄ : ∀ a ∈ u, 0 ≤ f₄)
  (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b)) (hs : s ⊆ u) (ht : t ⊆ u) :
  (∑ a in s, f₁ a) * (∑ b in t, f₂ b) ≤ (∑ a in s ∪ t, f₃ a) * (∑ b in s ∩ t, f₄ b) :=
begin
  sorry,
end

lemma fkg [fintype α] (hμ : 0 ≤ μ) (hf : monotone f) (hg : monotone g) :
  (∑ a, f a * μ a) * (∑ a, g a * μ a) ≤ (∑ a, f a * g a * μ a) * (∑ a, μ a) :=
begin
  sorry
end
