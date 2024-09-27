import Mathlib.Data.Set.Card

/-!
# TODO

Rename `Set.exists_subset_card_eq` to `Set.exists_subset_ncard_eq`
-/

open scoped Cardinal

namespace Set
variable {α : Type*} {s : Set α}

lemma exists_subset_natCard_eq {c : Cardinal} (hc : c ≤ #s) : ∃ t ⊆ s, #t = c :=
  Cardinal.le_mk_iff_exists_subset.mp hc

end Set
