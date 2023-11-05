import Mathlib.GroupTheory.Subgroup.Actions

namespace Subgroup
variable {G α : Type*} [Group G] [MulAction G α] {S : Subgroup G}

@[to_additive (attr := simp)]
lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end Subgroup
