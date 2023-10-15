import Mathlib.Order.UpperLower.Basic
import LeanCamCombi.Mathlib.Data.SetLike.Basic

/-!
### TODO

Explicitate `le` field in the `CompletelyDistributiveLattice` instances.
-/

namespace LowerSet
variable {α : Type*}
open Function Set

section LE
variable [LE α] {s t : LowerSet α} {a : α}

@[simp, norm_cast] lemma coe_mk (s : Set α) (hs) : (mk s hs : Set α) = s := rfl

@[norm_cast] lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t := Iff.rfl

@[simp, norm_cast] lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

-- TODO: Introduce an `IsMaxOn` predicate?
/-- Remove a maximal element from a lower set. -/
def erase (s : LowerSet α) (a : α) (has : ∀ b ∈ s, a ≤ b → a = b) : LowerSet α where
  carrier := s \ {a}
  lower' b c hcb hb :=
    ⟨s.lower hcb hb.1, by rintro (rfl : c = a); exact hb.2 (has _ hb.1 hcb).symm⟩

lemma erase_le {has} : s.erase a has ≤ s :=diff_subset _ _

lemma erase_lt {has} (ha : a ∈ s) : s.erase a has < s :=
  sdiff_lt (singleton_subset_iff.2 ha) $ singleton_ne_empty _

@[simp, norm_cast]
lemma coe_erase (s : LowerSet α) (a : α) (ha) : (s.erase a ha : Set α) = ↑s \ {a} := rfl

@[simp] lemma erase_idem (s : LowerSet α) (a : α) (ha) :
    ((s.erase a ha).erase a fun _b hb ↦ ha _ hb.1) = s.erase a ha :=
  SetLike.coe_injective sdiff_idem

end LE

section Preorder
variable [Preorder α] {s : LowerSet α} {a : α}

@[simp] lemma Iic_ne_bot (a : α) : Iic a ≠ ⊥ := SetLike.coe_ne_coe.1 nonempty_Iic.ne_empty
@[simp] lemma Iic_le : Iic a ≤ s ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.lower.Iic_subset ha⟩

@[simp]
lemma erase_sup_Iic (has) (ha : a ∈ s) : s.erase a has ⊔ Iic a = s := by
  refine' le_antisymm (sup_le erase_le $ Iic_le.2 ha) fun b hb ↦ _
  obtain rfl | hba := eq_or_ne b a
  · exact subset_union_right _ _ (mem_Iic.2 le_rfl)
  · exact subset_union_left _ _ ⟨hb, hba⟩

@[simp] lemma Iic_sup_erase (has) (ha : a ∈ s) : Iic a ⊔ s.erase a has = s := by
  rw [sup_comm, erase_sup_Iic _ ha]

end Preorder

section PartialOrder
variable [PartialOrder α] {a b : α}

nonrec lemma Iic_injective : Injective (Iic : α → LowerSet α) := fun _a _b hab ↦
  Iic_injective $ congr_arg ((↑) : _ → Set α) hab

@[simp] lemma Iic_inj : Iic a = Iic b ↔ a = b := Iic_injective.eq_iff

lemma Iic_ne_Iic : Iic a ≠ Iic b ↔ a ≠ b := Iic_inj.not

end PartialOrder
end LowerSet

namespace UpperSet
variable {α : Type*}
open Function Set

attribute [-instance] SetLike.instPartialOrder

section LE
variable [LE α] {s t : UpperSet α} {a : α}

@[simp, norm_cast] lemma coe_mk (s : Set α) (hs) : (mk s hs : Set α) = s := rfl

@[norm_cast] lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ t < s := Iff.rfl

@[norm_cast]
lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊤ := nonempty_iff_ne_empty.trans coe_eq_empty.not

-- TODO: Introduce an `IsMinOn` predicate?
/-- Remove a minimal element from a upper set. -/
def erase (s : UpperSet α) (a : α) (has : ∀ b ∈ s, b ≤ a → a = b) : UpperSet α where
  carrier := s \ {a}
  upper' b c hcb hb := ⟨s.upper hcb hb.1, by rintro (rfl : c = a); exact hb.2 (has _ hb.1 hcb).symm⟩

lemma le_erase {has} : s ≤ s.erase a has := diff_subset _ _

lemma lt_erase {has} (ha : a ∈ s) : s < s.erase a has :=
  coe_ssubset_coe.1 $ sdiff_lt (singleton_subset_iff.2 ha) $ singleton_ne_empty _

@[simp, norm_cast]
lemma coe_erase (s : UpperSet α) (a : α) (ha) : (s.erase a ha : Set α) = ↑s \ {a} := rfl

@[simp] lemma erase_idem (s : UpperSet α) (a : α) (ha) :
    ((s.erase a ha).erase a fun _b hb ↦ ha _ hb.1) = s.erase a ha :=
  SetLike.coe_injective sdiff_idem

end LE

section Preorder
variable [Preorder α] {s : UpperSet α} {a : α}

@[simp] lemma Ici_ne_top (a : α) : Ici a ≠ ⊤ := SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty

@[simp] lemma le_Ici : s ≤ Ici a ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.upper.Ici_subset ha⟩

@[simp] lemma erase_inf_Ici (has) (ha : a ∈ s) : s.erase a has ⊓ Ici a = s := by
  refine' le_antisymm _ (le_inf le_erase $ le_Ici.2 ha)
  rintro b hb
  obtain rfl | hba := eq_or_ne b a
  · exact subset_union_right _ _ (mem_Ici.2 le_rfl)
  · exact subset_union_left _ _ ⟨hb, hba⟩

@[simp] lemma Ici_inf_erase (has) (ha : a ∈ s) : Ici a ⊓ s.erase a has = s := by
  rw [inf_comm, erase_inf_Ici _ ha]

end Preorder

section PartialOrder
variable [PartialOrder α] {a b : α}

nonrec lemma Ici_injective : Injective (Ici : α → UpperSet α) := fun _a _b hab ↦
  Ici_injective $ congr_arg ((↑) : _ → Set α) hab

@[simp] lemma Ici_inj : Ici a = Ici b ↔ a = b := Ici_injective.eq_iff

lemma Ici_ne_Ici : Ici a ≠ Ici b ↔ a ≠ b := Ici_inj.not

end PartialOrder
end UpperSet
