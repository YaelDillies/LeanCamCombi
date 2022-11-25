import algebra.big_operators.basic

open_locale big_operators

namespace finset
variables {α β : Type*} [comm_monoid β]

@[to_additive] lemma prod_eq_pow_card (s : finset α) (f : α → β) (m : β) (h : ∀ x ∈ s, f x = m) :
  ∏ a in s, f a = m ^ s.card :=
(prod_congr rfl h).trans $ prod_const _

end finset
