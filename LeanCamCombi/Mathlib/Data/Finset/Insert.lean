import Mathlib.Data.Finset.Insert

namespace Finset
variable {α : Type*} [DecidableEq α]

instance Nontrivial.instDecidablePred : DecidablePred (Finset.Nontrivial (α := α)) :=
  inferInstanceAs (DecidablePred fun s ↦ ∃ a ∈ s, ∃ b ∈ s, a ≠ b)

lemma insert_comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  mod_cast Set.insert_comm a b s

end Finset
