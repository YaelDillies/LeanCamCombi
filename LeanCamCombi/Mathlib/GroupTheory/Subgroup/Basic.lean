import Mathlib.GroupTheory.Subgroup.Basic

--TODO: Fix implicitness `Subgroup.closure_eq_bot_iff`
--TODO: Fix implicitness `Subgroup.closure_eq_bot_iff`
namespace Subgroup
variable {G : Type*} [Group G]

attribute [norm_cast] coe_eq_univ AddSubgroup.coe_eq_univ

@[to_additive (attr := simp)] lemma coeSort_coe (s : Subgroup G) : ↥(s : Set G) = ↥s := rfl

end Subgroup
