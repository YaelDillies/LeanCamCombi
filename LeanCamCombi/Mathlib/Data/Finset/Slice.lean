import Mathlib.Data.Finset.Slice

variable {α : Type _}

namespace Set

#print Set.sized_empty /-
theorem sized_empty (r : ℕ) : (∅ : Set (Finset α)).Sized r := fun s hs => hs.elim
-/

end Set
