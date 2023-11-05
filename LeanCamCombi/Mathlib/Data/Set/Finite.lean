import Mathlib.Data.Set.Finite

namespace Set
variable {α : Type*} [Infinite α] {s : Set α}

lemma Finite.exists_not_mem (hs : s.Finite) : ∃ a, a ∉ s := by
  by_contra' h; exact infinite_univ (hs.subset fun a _ => h _)

end Set

namespace Finset
variable {α : Type*} [Infinite α]

lemma exists_not_mem (s : Finset α) : ∃ a, a ∉ s := s.finite_toSet.exists_not_mem

lemma exists_card : ∀ n : ℕ, ∃ s : Finset α, s.card = n
  | 0 => ⟨∅, card_empty⟩
  | n + 1 => by
    classical
    obtain ⟨s, rfl⟩ := exists_card n
    obtain ⟨a, ha⟩ := s.exists_not_mem
    exact ⟨insert a s, card_insert_of_not_mem ha⟩

end Finset
