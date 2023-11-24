import Mathlib.Combinatorics.Colex

variable {α : Type*}

namespace Finset
namespace Colex
section LinearOrder
variable [LinearOrder α]

instance [Fintype α] : BoundedOrder (Colex α) where
    top := toColex univ
    le_top _x := toColex_le_toColex_of_subset $ subset_univ _

@[simp] lemma toColex_univ [Fintype α] : toColex (univ : Finset α) = ⊤ := rfl
@[simp] lemma ofColex_top [Fintype α] : ofColex (⊤ : Colex α) = univ := rfl

end LinearOrder
end Colex
end Finset
