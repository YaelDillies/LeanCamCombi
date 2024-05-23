import Mathlib.Order.Interval.Finset.Basic

-- TODO: Rename `Prod.Icc_eq` to `Finset.Icc_prod_eq` to match `Set.Icc_prod_eq`

namespace Finset
variable {α β : Type*} [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [@DecidableRel α (· ≤ ·)] [@DecidableRel β (· ≤ ·)]

lemma prod_Icc (a b : α × β) : Icc a b = (Icc a.fst b.fst).product (Icc a.snd b.snd) :=
  Prod.Icc_eq _ _

end Finset
