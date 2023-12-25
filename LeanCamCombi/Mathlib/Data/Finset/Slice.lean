import Mathlib.Data.Finset.Slice

#align_import mathlib.data.finset.slice

variable {α : Type _}

namespace Set

#print Set.sized_empty /-
theorem sized_empty (r : ℕ) : (∅ : Set (Finset α)).Sized r := fun s hs => hs.elim
-/

end Set
