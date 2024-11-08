import Mathlib.Data.Finset.Basic

namespace Finset

nonrec lemma Nontrivial.nonempty {α} {X : Finset α} (hX : X.Nontrivial) : X.Nonempty := hX.nonempty

attribute [simp] subset_empty

end Finset
