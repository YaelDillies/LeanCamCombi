import Mathlib.Data.Finset.Pointwise
import LeanCamCombi.Mathlib.GroupTheory.QuotientGroup

open Function Set
open scoped Pointwise

namespace MulAction
variable {α β γ : Type*} [Group α] [MulAction α β] [MulAction α γ] {a : α}

section Set

@[to_additive (attr := simp)]
lemma stabilizer_empty : stabilizer α (∅ : Set β) = ⊤ :=
  Subgroup.coe_eq_univ.1 <| eq_univ_of_forall fun _a => smul_set_empty

@[to_additive (attr := simp)]
lemma stabilizer_singleton (b : β) : stabilizer α ({b} : Set β) = stabilizer α b := by ext; simp

@[to_additive]
lemma mem_stabilizer_set {s : Set β} : a ∈ stabilizer α s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  refine' ⟨fun h b => _, fun h => _⟩
  · rw [← (smul_mem_smul_set_iff : a • b ∈ a • s ↔ _), mem_stabilizer_iff.1 h]
  simp_rw [mem_stabilizer_iff, Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

@[to_additive (attr := simp)]
lemma stabilizer_subgroup (s : Subgroup α) : stabilizer α (s : Set α) = s := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine' fun a => ⟨fun h => _, fun ha b => s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

@[to_additive]
lemma map_stabilizer_le (f : α →* α) (s : Set α) :
    (stabilizer α s).map f ≤ stabilizer α (f '' s) := by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, exists_prop, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib, ha]

@[to_additive (attr := simp)]
lemma stabilizer_mul (s : Set α) : (stabilizer α s : Set α) * s = s := by
  ext
  refine' ⟨_, fun h => ⟨_, _, (stabilizer α s).one_mem, h, one_mul _⟩⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

@[to_additive]
lemma le_stabilizer_smul_left [SMul β γ] [IsScalarTower α β γ] (b : β) (c : γ) :
    stabilizer α b ≤ stabilizer α (b • c) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, ← smul_assoc]; rintro a h; rw [h]

@[to_additive (attr := simp)]
lemma stabilizer_mul_eq_left [Group β] [IsScalarTower α β β] (b c : β) :
    stabilizer α (b * c) = stabilizer α b := by
  rw [← smul_eq_mul]
  refine' (le_stabilizer_smul_left _ _).antisymm' fun a ha => _
  simpa only [smul_eq_mul, mem_stabilizer_iff, ← smul_mul_assoc, mul_left_inj] using ha

end Set

@[to_additive]
lemma le_stabilizer_smul_right {α} [Group α] [MulAction α γ] [SMul β γ] [SMulCommClass α β γ]
    (b : β) (c : γ) : stabilizer α c ≤ stabilizer α (b • c) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, smul_comm]; rintro a h; rw [h]

@[to_additive (attr := simp)]
lemma stabilizer_smul_eq_right {α} [Group α] [Group β] [MulAction α γ] [MulAction β γ]
    [SMulCommClass α β γ] (b : β) (c : γ) : stabilizer α (b • c) = stabilizer α c :=
  (le_stabilizer_smul_right _ _).antisymm' <|
    (le_stabilizer_smul_right b⁻¹ _).trans_eq <| by rw [inv_smul_smul]

section DecidableEq
variable [DecidableEq β]

@[to_additive (attr := simp)]
lemma stabilizer_coe_finset (s : Finset β) : stabilizer α (s : Set β) = stabilizer α s := by
  ext; simp [←Finset.coe_inj]

@[to_additive (attr := simp)]
lemma stabilizer_finset_empty : stabilizer α (∅ : Finset β) = ⊤ :=
  Subgroup.coe_eq_univ.1 <| eq_univ_of_forall Finset.smul_finset_empty

@[to_additive (attr := simp)]
lemma stabilizer_finset_singleton (b : β) : stabilizer α ({b} : Finset β) = stabilizer α b := by
  ext; simp

@[to_additive]
lemma mem_stabilizer_finset {s : Finset β} : a ∈ stabilizer α s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  simp_rw [← stabilizer_coe_finset, mem_stabilizer_set, Finset.mem_coe]

@[to_additive]
lemma mem_stabilizer_finset_iff_subset_smul_finset {s : Finset β} :
    a ∈ stabilizer α s ↔ s ⊆ a • s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le, eq_comm]

@[to_additive]
lemma mem_stabilizer_finset_iff_smul_finset_subset {s : Finset β} :
    a ∈ stabilizer α s ↔ a • s ⊆ s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).ge]

@[to_additive]
lemma mem_stabilizer_finset' {s : Finset β} : a ∈ stabilizer α s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← Subgroup.inv_mem_iff, mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

end DecidableEq

@[to_additive]
lemma mem_stabilizer_set_iff_subset_smul_set {s : Set β} (hs : s.Finite) :
    a ∈ stabilizer α s ↔ s ⊆ a • s := by
  sorry
  -- lift s to Finset β using hs
  -- classical
  -- norm_cast
  -- simp only [stabilizer_coe_finset, mem_stabilizer_finset_iff_subset_smul_finset]

@[to_additive]
lemma mem_stabilizer_set_iff_smul_set_subset {s : Set β} (hs : s.Finite) :
    a ∈ stabilizer α s ↔ a • s ⊆ s := by
  sorry
  -- lift s to Finset β using hs
  -- classical
  -- norm_cast
  -- simp [-mem_stabilizer_iff, mem_stabilizer_finset_iff_smul_finset_subset]

@[to_additive]
lemma mem_stabilizer_set' {s : Set β} (hs : s.Finite) :
    a ∈ stabilizer α s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  lift s to Finset β using hs
  classical simp [-mem_stabilizer_iff, mem_stabilizer_finset']

end MulAction

namespace MulAction
variable {α : Type*} [CommGroup α] {s : Set α}

@[to_additive (attr := simp)]
lemma mul_stabilizer (s : Set α) : s * (stabilizer α s : Set α) = s := by
  rw [mul_comm, stabilizer_mul]

@[to_additive]
lemma stabilizer_image_coe_quotient (s : Set α) :
    stabilizer (α ⧸ stabilizer α s) (((↑) : α → α ⧸ stabilizer α s) '' s) = ⊥ := by
  ext a
  induction' a using QuotientGroup.induction_on' with a
  simp only [mem_stabilizer_iff, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have : (a : α ⧸ stabilizer α s) • ((↑) : α → α ⧸ stabilizer α s) '' s = (↑) '' (a • s) :=
    (image_smul_distrib (QuotientGroup.mk' <| stabilizer α s) _ _).symm
  rw [this]
  refine' ⟨fun h => _, fun h => by rw [h]⟩
  rwa [Subgroup.image_coe_inj, mul_smul_comm, stabilizer_mul] at h

end MulAction
