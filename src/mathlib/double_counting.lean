import combinatorics.double_counting

open function

namespace finset
variables {α β : Type*} (r : α → β → Prop) (s : finset α) (t : finset β) (a a' : α) (b b' : β)
  [decidable_pred (r a)] [Π a, decidable (r a b)]

@[simp, norm_cast] lemma coe_bipartite_below : (s.bipartite_below r b : set α) = {a ∈ s | r a b} :=
coe_filter _ _

@[simp, norm_cast] lemma coe_bipartite_above : (t.bipartite_above r a : set β) = {b ∈ t | r a b} :=
coe_filter _ _

variables {s t}

lemma card_le_card_of_forall_subsingleton [Π a b, decidable (r a b)]
  (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b) (ht : ∀ b ∈ t, ({a ∈ s | r a b} : set α).subsingleton) :
  s.card ≤ t.card :=
by simpa using card_mul_le_card_mul _ (λ a h, card_pos.2 $
  (by { rw [←coe_nonempty, coe_bipartite_above], exact hs _ h } : (t.bipartite_above r a).nonempty))
  (λ b h, card_le_one.2 $ by { simp_rw mem_bipartite_below, exact ht _ h })

lemma card_le_card_of_forall_subsingleton' [Π a b, decidable (r a b)]
  (ht : ∀ b ∈ t, ∃ a, a ∈ s ∧ r a b) (hs : ∀ a ∈ s, ({b ∈ t | r a b} : set β).subsingleton) :
  t.card ≤ s.card :=
card_le_card_of_forall_subsingleton (swap r) ht hs

end finset
