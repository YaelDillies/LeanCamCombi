import Mathlib.Algebra.Group.Subgroup.Pointwise

open Set
open scoped Pointwise

namespace Subgroup
variable {G H S : Type*} [Group G] {s : Subgroup G} {a : G}

@[norm_cast, to_additive]
lemma coe_set_eq_one : (s : Set G) = 1 ↔ s = ⊥ := (SetLike.ext'_iff.trans (by rfl)).symm

section Group
variable [Group H] [SetLike S H] [SubgroupClass S H] {s : S} {a b : G}

/-!
Annoyingly, it seems like the following two pairs of lemmas cannot be unified.
-/

section Left
variable [MulAction G H] [IsScalarTower G H H]

/-- See `Subgroup.disjoint_smul_of_ne'` for a version that works for the right action of a group on
itself. -/
@[to_additive "See `AddSubgroup.disjoint_vadd_of_ne'` for a version that works for the right action
of a group on itself."]
lemma disjoint_smul_of_ne (hab : a • (s : Set H) ≠ b • s) : Disjoint (a • s : Set H) (b • s) := by
  simp only [disjoint_left]
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe_set hc, ← smul_assoc, ← hcd, smul_assoc, smul_coe_set hc, smul_coe_set hd]

/-- See `Subgroup.pairwiseDisjoint_smul'` for a version that works for the right action of a group
on itself. -/
@[to_additive "See `AddSubgroup.pairwiseDisjoint_vadd'` for a version that works for the right
action of a group on itself."]
lemma pairwiseDisjoint_smul (s : S) :
    (Set.range fun a : G ↦ a • (s : Set H)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact disjoint_smul_of_ne

end Left

section Right
variable [MulAction G H] [IsScalarTower G Hᵐᵒᵖ H]

open MulOpposite

/-- See `Subgroup.disjoint_smul_of_ne` for a version that works for the left action of a group on
itself. -/
@[to_additive "See `AddSubgroup.disjoint_vadd_of_ne` for a version that works for the left action
of a group on itself."]
lemma disjoint_smul_of_ne' (hab : a • (s : Set H) ≠ b • s) :
    Disjoint (a • s : Set H) (b • s) := by
  simp only [disjoint_left]
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← op_smul_coe_set hc, ← smul_assoc, ← op_smul, ← hcd, op_smul, smul_assoc, op_smul_coe_set hc,
    op_smul_coe_set hd]

/-- See `Subgroup.pairwiseDisjoint_smul` for a version that works for the left action of a group on
itself. -/
@[to_additive "See `AddSubgroup.pairwiseDisjoint_vadd` for a version that works for the left action
of a group on itself."]
lemma pairwiseDisjoint_smul' (s : S) :
    (Set.range fun a : G ↦ a • (s : Set H)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact disjoint_smul_of_ne'

end Right
end Group
end Subgroup
