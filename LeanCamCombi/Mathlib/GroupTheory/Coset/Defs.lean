import Mathlib.GroupTheory.Coset.Defs

variable {α : Type*}

namespace QuotientGroup
variable [Group α] (s : Subgroup α)

@[to_additive]
instance [DecidablePred (· ∈ s)] : DecidableEq (α ⧸ s) :=
  @Quotient.decidableEq _ _ (QuotientGroup.leftRelDecidable _)

end QuotientGroup
