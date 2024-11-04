import Mathlib.Data.Finset.Basic

nonrec lemma Finset.Nontrivial.nonempty {α} {X : Finset α} (hX : X.Nontrivial) : X.Nonempty :=
  hX.nonempty
