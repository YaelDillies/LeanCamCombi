import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Data.Finset.Lattice
import LeanCamCombi.Mathlib.Data.Finset.Basic

namespace Finset
variable {α : Type*}

/-- See also `Finset.family_induction_on`. -/
@[elab_as_elim]
lemma memberFamily_induction_on {p : Finset (Finset α) → Prop} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.nonMemberSubfamily a) → p (𝒜.memberSubfamily a) → p 𝒜) :
    p 𝒜 := by
  set u := 𝒜.sup id
  have hu : ∀ s ∈ 𝒜, s ⊆ u := fun s ↦ le_sup (f := id)
  clear_value u
  induction' u using Finset.induction with a u _ ih generalizing 𝒜
  · simp_rw [subset_empty] at hu
    rw [←subset_singleton_iff', subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  refine subfamily a (ih _ ?_) (ih _ ?_)
  · simp only [mem_nonMemberSubfamily, and_imp]
    exact fun s hs has ↦ (subset_insert_iff_of_not_mem has).1 $ hu _ hs
  · simp only [mem_memberSubfamily, and_imp]
    exact fun s hs ha ↦ (insert_subset_insert_iff ha).1 $ hu _ hs

end Finset
