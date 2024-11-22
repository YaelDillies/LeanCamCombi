import Mathlib.Algebra.Pointwise.Stabilizer

open Set
open scoped Pointwise

namespace MulAction
variable {G H α : Type*}

section Group
variable [Group G] [Group H] [MulAction G α] {s t : Set α} {a : G}

attribute [norm_cast] stabilizer_coe_finset

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_union :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∪ t) := by
  aesop (add simp [SetLike.le_def, smul_set_union])

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_inter :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∩ t) := by
  aesop (add simp [SetLike.le_def, smul_set_inter])

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_sdiff :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s \ t) := by
  aesop (add simp [SetLike.le_def, smul_set_sdiff])

@[to_additive]
lemma stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s ≤ stabilizer G t)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G t) :
    stabilizer G (s ∪ t) = stabilizer G s := by
  refine le_antisymm ?_ ?_
  · calc
      stabilizer G (s ∪ t)
        ≤ stabilizer G (s ∪ t) ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G ((s ∪ t) \ t) := stabilizer_inf_stabilizer_le_stabilizer_sdiff
      _ = stabilizer G s := by rw [union_diff_cancel_right]; simpa [← disjoint_iff_inter_eq_empty]
  · calc
      stabilizer G s
        ≤ stabilizer G s ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G (s ∪ t) := stabilizer_inf_stabilizer_le_stabilizer_union

@[to_additive]
lemma stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t ≤ stabilizer G s)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G s)  :
    stabilizer G (s ∪ t) = stabilizer G t := by
  rw [union_comm, stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

-- TODO: Replace `mem_stabilizer_of_finite_iff_smul_le`
@[to_additive]
lemma mem_stabilizer_iff_subset_smul_set (hs : s.Finite) : a ∈ stabilizer G s ↔ s ⊆ a • s := by
  classical
  lift s to Finset α using hs
  norm_cast
  exact mem_stabilizer_finset_iff_subset_smul_finset

@[to_additive]
lemma mem_stabilizer_iff_smul_set_subset (hs : s.Finite) : a ∈ stabilizer G s ↔ a • s ⊆ s := by
  classical
  lift s to Finset α using hs
  norm_cast
  exact mem_stabilizer_finset_iff_smul_finset_subset

variable {s t : Set G}

open scoped RightActions in
@[to_additive]
lemma op_smul_set_stabilizer_subset (ha : a ∈ s) : (stabilizer G s : Set G) <• a ⊆ s :=
  smul_set_subset_iff.2 fun b hb ↦ by rw [← hb]; exact smul_mem_smul_set ha

@[to_additive]
lemma stabilizer_subset_div_right (ha : a ∈ s) : ↑(stabilizer G s) ⊆ s / {a} := fun b hb ↦
  ⟨_, by rwa [← smul_eq_mul, mem_stabilizer_set.1 hb], _, mem_singleton _, mul_div_cancel_right _ _⟩

@[to_additive]
lemma stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : Set G).Finite := by
  obtain ⟨a, ha⟩ := hs₀
  exact (hs.div <| finite_singleton _).subset <| stabilizer_subset_div_right ha

end Group

section CommGroup
variable [CommGroup G] {s t : Set G} {a : G}

@[to_additive]
lemma smul_set_stabilizer_subset (ha : a ∈ s) : a • (stabilizer G s : Set G) ⊆ s := by
  simpa using op_smul_set_stabilizer_subset ha

end CommGroup
end MulAction
