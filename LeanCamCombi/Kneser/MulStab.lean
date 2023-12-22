/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import Mathlib.GroupTheory.Subgroup.Actions
import LeanCamCombi.Mathlib.GroupTheory.Subgroup.Stabilizer
import LeanCamCombi.Kneser.Mathlib

/-!
# Stabilizer of a finset

This file defines the stabilizer of a finset of a group as a finset.

## Main declarations

* `finset.mulStab`: The stabilizer of a **nonempty** finset as a finset.
-/

open Function MulAction
open scoped Pointwise

namespace Finset
variable {ι α : Type*}

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`.-/
@[to_additive "The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`."]
def mulStab (s : Finset α) : Finset α := (s / s).filter fun a => a • s = s

@[to_additive (attr := simp)]
lemma mem_mulStab (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s = s := by
  rw [mulStab, mem_filter, mem_div, and_iff_right_of_imp]
  obtain ⟨b, hb⟩ := hs
  exact fun h => ⟨_, _, by rw [← h]; exact smul_mem_smul_finset hb, hb, mul_div_cancel'' _ _⟩

@[to_additive]
lemma mulStab_subset_div : s.mulStab ⊆ s / s := filter_subset _ _

@[to_additive]
lemma mulStab_subset_div_right (ha : a ∈ s) : s.mulStab ⊆ s / {a} := by
  refine' fun b hb => mem_div.2 ⟨_, _, _, mem_singleton_self _, mul_div_cancel'' _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rw [← hb]
  exact smul_mem_smul_finset ha

@[to_additive (attr := simp)]
lemma coe_mulStab (hs : s.Nonempty) : (s.mulStab : Set α) = MulAction.stabilizer α s := by
  ext; simp [mem_mulStab hs]

@[to_additive]
lemma mem_mulStab_iff_subset_smul_finset (hs : s.Nonempty) : a ∈ s.mulStab ↔ s ⊆ a • s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, mem_stabilizer_finset_iff_subset_smul_finset]

@[to_additive]
lemma mem_mulStab_iff_smul_finset_subset (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s ⊆ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, mem_stabilizer_finset_iff_smul_finset_subset]

@[to_additive]
lemma mem_mulStab' (hs : s.Nonempty) : a ∈ s.mulStab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, mem_stabilizer_finset']

@[to_additive (attr := simp)]
lemma mulStab_empty : mulStab (∅ : Finset α) = ∅ := by simp [mulStab]

@[to_additive (attr := simp)]
lemma mulStab_singleton (a : α) : mulStab ({a} : Finset α) = 1 := by
  simp [mulStab, singleton_one]

@[to_additive]
lemma Nonempty.of_mulStab : s.mulStab.Nonempty → s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, not_imp_not]; rintro rfl; exact mulStab_empty

@[to_additive (attr := simp)]
lemma one_mem_mulStab : (1 : α) ∈ s.mulStab ↔ s.Nonempty :=
  ⟨fun h => Nonempty.of_mulStab ⟨_, h⟩, fun h => (mem_mulStab h).2 <| one_smul _ _⟩

@[to_additive] protected alias ⟨_, Nonempty.one_mem_mulStab⟩ := one_mem_mulStab

@[to_additive]
lemma Nonempty.mulStab (h : s.Nonempty) : s.mulStab.Nonempty := ⟨_, h.one_mem_mulStab⟩

@[to_additive (attr := simp)]
lemma mulStab_nonempty : s.mulStab.Nonempty ↔ s.Nonempty := ⟨Nonempty.of_mulStab, Nonempty.mulStab⟩

@[to_additive (attr := simp)]
lemma card_mulStab_eq_one : s.mulStab.card = 1 ↔ s.mulStab = 1 := by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨a, ha⟩ := card_eq_one.1 h
    rw [ha]
    rw [eq_singleton_iff_nonempty_unique_mem, mulStab_nonempty, ← one_mem_mulStab] at ha
    rw [← ha.2 _ ha.1, singleton_one]
  · rw [h, card_one]

@[to_additive]
lemma Nonempty.mulStab_nontrivial (h : s.Nonempty) : s.mulStab.Nontrivial ↔ s.mulStab ≠ 1 :=
  nontrivial_iff_ne_singleton h.one_mem_mulStab

@[to_additive]
lemma subset_mulStab_mul_left (ht : t.Nonempty) : s.mulStab ⊆ (s * t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  simp_rw [subset_iff, mem_mulStab hs, mem_mulStab (hs.mul ht)]
  rintro a h
  rw [← smul_mul_assoc, h]

@[to_additive (attr := simp)]
lemma mulStab_mul (s : Finset α) : s.mulStab * s = s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact mul_empty _
  refine' coe_injective _
  simp only [hs, coe_mul, coe_mulStab, ← stabilizer_coe_finset, stabilizer_mul]

@[to_additive]
lemma mul_subset_right_iff (ht : t.Nonempty) : s * t ⊆ t ↔ s ⊆ t.mulStab := by
  simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_subset,
    ←mem_mulStab_iff_smul_finset_subset ht, subset_iff]

@[to_additive]
lemma mul_subset_right : s ⊆ t.mulStab → s * t ⊆ t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  · exact (mul_subset_right_iff ht).2

@[to_additive]
lemma smul_mulStab (ha : a ∈ s.mulStab) : a • s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe] at ha
  rw [← coe_inj, coe_smul_finset, coe_mulStab hs, Subgroup.smul_coe ha]

@[to_additive (attr := simp)]
lemma mulStab_mul_mulStab (s : Finset α) : s.mulStab * s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_congr rfl fun _ => smul_mulStab,
      ← sup_eq_biUnion, sup_const hs.mulStab]

@[to_additive]
lemma inter_mulStab_subset_mulStab_union : s.mulStab ∩ t.mulStab ⊆ (s ∪ t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  intro x hx
  rw [mem_mulStab (Finset.Nonempty.mono (subset_union_left s t) hs), smul_finset_union,
    (mem_mulStab hs).mp (mem_of_mem_inter_left hx),
    (mem_mulStab ht).mp (mem_of_mem_inter_right hx)]

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
lemma mulStab_subset_div_left (ha : a ∈ s) : s.mulStab ⊆ {a} / s := by
  refine' fun b hb => mem_div.2 ⟨_, _, mem_singleton_self _, _, div_div_cancel _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rwa [← hb, ← inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha

@[to_additive]
lemma subset_mulStab_mul_right (hs : s.Nonempty) : t.mulStab ⊆ (s * t).mulStab := by
  rw [mul_comm]; exact subset_mulStab_mul_left hs

@[to_additive (attr := simp)]
lemma mul_mulStab (s : Finset α) : s * s.mulStab = s := by rw [mul_comm]; exact mulStab_mul _

@[to_additive (attr := simp)]
lemma mul_mulStab_mul_mul_mul_mulStab_mul :
    s * (s * t).mulStab * (t * (s * t).mulStab) = s * t := by
  rw [mul_mul_mul_comm, mulStab_mul_mulStab, mul_mulStab]

@[to_additive]
lemma smul_finset_mulStab_subset (ha : a ∈ s) : a • s.mulStab ⊆ s :=
  (smul_finset_subset_smul ha).trans s.mul_mulStab.subset'

@[to_additive]
lemma mul_subset_left_iff (hs : s.Nonempty) : s * t ⊆ s ↔ t ⊆ s.mulStab := by
  rw [mul_comm, mul_subset_right_iff hs]

@[to_additive]
lemma mul_subset_left : t ⊆ s.mulStab → s * t ⊆ s := by rw [mul_comm]; exact mul_subset_right

@[to_additive (attr := simp)]
lemma mulStab_idem (s : Finset α) : s.mulStab.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine' coe_injective _
  rw [coe_mulStab hs, coe_mulStab hs.mulStab, ← stabilizer_coe_finset, coe_mulStab hs]
  simp

@[to_additive (attr := simp)]
lemma mulStab_smul (a : α) (s : Finset α) : (a • s).mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine' coe_injective _
  rw [coe_mulStab hs, coe_mulStab hs.smul_finset, stabilizer_smul_eq_right]

open scoped Classical

@[to_additive]
lemma mulStab_image_coe_quotient (hs : s.Nonempty) :
    (s.image (↑) : Finset (α ⧸ stabilizer α s)).mulStab = 1 := by
  refine' coe_injective _
  rw [coe_mulStab (hs.image _), ← stabilizer_coe_finset, ← stabilizer_coe_finset, coe_image,
    coe_one, stabilizer_image_coe_quotient, Subgroup.coe_bot, Set.singleton_one]

@[to_additive]
lemma to_name_mul (s t : Finset α) (ht : t.Nonempty) :
    QuotientGroup.mk ⁻¹' ((↑) '' (s : Set α) : Set (α ⧸ stabilizer α t)) = s * t.mulStab := by
  convert (stabilizer α t).mul_alt_version s
  refine' Eq.trans _ (Set.iUnion_subtype _ _).symm
  simp_rw [Subgroup.mk_smul, ← SetLike.mem_coe, ← coe_mulStab ht, ← coe_smul_finset, ← coe_biUnion,
    biUnion_smul_finset, smul_eq_mul, coe_mul, mul_comm]

@[to_additive]
lemma to_name_mul_also (s t : Finset α) :
    QuotientGroup.mk ⁻¹' ((↑) '' ((s : Set α) * (t : Set α)) : Set (α ⧸ stabilizer α (s * t)))
      = ↑s * ↑t := by
  sorry
  -- obtain rfl | hs := s.eq_empty_or_nonempty
  -- · simp
  -- obtain rfl | ht := t.eq_empty_or_nonempty
  -- · simp
  -- convert to_name_mul (s * t) (s * t) (hs.mul ht) using 1
  -- · simp
  -- · norm_cast
  --   rw [mul_mulStab (s * t)]

@[to_additive]
lemma pairwiseDisjoint_smul_finset_mulStab (s : Finset α) :
    (Set.range fun a : α => a • s.mulStab).PairwiseDisjoint id := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [onFun, id_eq]
  simp_rw [← disjoint_coe, ← coe_injective.ne_iff, coe_smul_finset, coe_mulStab hs]
  exact Subgroup.pairwiseDisjoint_smul _ (Set.mem_range_self _) (Set.mem_range_self _)

@[to_additive]
lemma disjoint_smul_finset_mulStab_mul_mulStab :
    ¬a • s.mulStab ⊆ t * s.mulStab → Disjoint (a • s.mulStab) (t * s.mulStab) := by
  simp_rw [@not_imp_comm (_ ⊆ _), ← smul_eq_mul, ← biUnion_smul_finset, disjoint_biUnion_right,
    Classical.not_forall]
  rintro ⟨b, hb, h⟩
  rw [s.pairwiseDisjoint_smul_finset_mulStab.eq (Set.mem_range_self _) (Set.mem_range_self _) h]
  exact subset_biUnion_of_mem (· • mulStab s) hb

@[to_additive]
lemma card_mulStab_dvd_card_mul_mulStab (s t : Finset α) :
    t.mulStab.card ∣ (s * t.mulStab).card :=
  card_dvd_card_smul_right <|
    t.pairwiseDisjoint_smul_finset_mulStab.subset <| Set.image_subset_range _ _

@[to_additive]
lemma card_mulStab_dvd_card (s : Finset α) : s.mulStab.card ∣ s.card := by
  simpa only [mul_mulStab] using s.card_mulStab_dvd_card_mul_mulStab s

@[to_additive]
lemma card_mulStab_le_card : s.mulStab.card ≤ s.card := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rfl
  · exact Nat.le_of_dvd hs.card_pos s.card_mulStab_dvd_card

/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.mulStab`. -/
@[to_additive
      "A fintype instance for the stabilizer of a nonempty finset `s` in terms of\n`s.add_stab`."]
private def fintype_stabilizer_of_mulStab (hs : s.Nonempty) : Fintype (stabilizer α s)
    where
  elems :=
    s.mulStab.attach.map
      ⟨Subtype.map id fun _ => (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩
  complete a :=
    mem_map.2
      ⟨⟨_, (mem_mulStab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mulStab hs).2 a.2⟩, Subtype.ext rfl⟩

@[to_additive]
lemma card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    s.mulStab.card ∣ t.mulStab.card := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  rw [← coe_subset, coe_mulStab hs, coe_mulStab ht, SetLike.coe_subset_coe] at h
  letI : Fintype (stabilizer α s) := fintype_stabilizer_of_mulStab hs
  letI : Fintype (stabilizer α t) := fintype_stabilizer_of_mulStab ht
  convert Subgroup.card_dvd_of_le h using 1 <;> exact ((card_map _).trans card_attach).symm

/-- A version of Lagrange's lemma. -/
@[to_additive "A version of Lagrange's lemma."]
lemma card_mul_card_image_coe' (s t : Finset α) :
    t.mulStab.card * (s.image (↑) : Finset (α ⧸ stabilizer α t)).card = (s * t.mulStab).card := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have :=
    QuotientGroup.preimageMkEquivSubgroupProdSet (stabilizer α t)
      ((↑) '' (s : Set α) : Set (α ⧸ stabilizer α t))
  have that : ↥(stabilizer α t) = ↥t.mulStab := by
    rw [←SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans (Equiv.prodCongr (Equiv.cast that) (Equiv.refl _))
  rw [to_name_mul s t ht] at temp
  replace temp := Fintype.card_congr temp
  simp only [← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe] at temp
  sorry
  -- rw [← temp]
  -- simp only [Fintype.card_ofFinset, mem_coe, iff_self_iff, forall_const]

-- TODO: Fix `Lean.Internal.coeM` leak

@[to_additive]
lemma card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    (s * t).card =
      (s * t).mulStab.card * ((s * t).image (↑) : Finset (α ⧸ stabilizer α (s * t))).card := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet (stabilizer α (s * t)) $
    (↑) '' (s * t : Set α)
  have that : ↥(stabilizer α (s * t)) = ↥(s * t).mulStab := by
    rw [←SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans (Equiv.prodCongr (Equiv.cast that) (Equiv.refl _))
  sorry
  -- rw [to_name_mul_also s t] at temp
  -- replace temp := Fintype.card_congr temp
  -- have h1 : Fintype.card ((s * t : Finset α) : Set α) = Fintype.card (s * t) := by congr
  -- simp_rw [← coe_mul s t, h1, Fintype.card_coe, coe_mul, Fintype.card_prod, Fintype.card_ofFinset,
  --   Fintype.card_coe, ← coe_mul s t, to_finset_coe] at temp
  -- exact temp

/-- A version of Lagrange's lemma. -/
@[to_additive "A version of Lagrange's lemma."]
lemma card_mul_card_image_coe (s t : Finset α) :
    (s * t).mulStab.card * (s.image (↑) * t.image (↑) : Finset (α ⧸ stabilizer α (s * t))).card =
      (s * t).card := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have :=
    QuotientGroup.preimageMkEquivSubgroupProdSet (stabilizer α (s * t))
      (((s : Set α).image (↑) : Set (α ⧸ stabilizer α (s * t))) *
        ((t : Set α).image (↑) : Set (α ⧸ stabilizer α (s * t))))
  have image_coe_mul :
    (((s : Set α) * t).image (↑) : Set (α ⧸ stabilizer α (s * t))) =
      (s : Set α).image (↑) * (t : Set α).image (↑) :=
    sorry
    -- Set.image_mul (QuotientGroup.mk' (stabilizer α (s * t)) : α →* α ⧸ stabilizer α (s * t))
  rw [← image_coe_mul, to_name_mul_also, image_coe_mul] at this
  have that :
    (stabilizer α (s * t) ×
        ↥(((s : Set α).image (↑) : Set (α ⧸ stabilizer α (s * t))) *
            ((t : Set α).image (↑) : Set (α ⧸ stabilizer α (s * t))))) =
      ((s * t).mulStab ×
        ↥(((s : Set α).image (↑) : Set (α ⧸ stabilizer α (s * t))) *
            ((t : Set α).image (↑) : Set (α ⧸ stabilizer α (s * t))))) := by rw [←SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans (Equiv.cast that)
  replace temp := Fintype.card_congr temp
  simp_rw [← Finset.coe_mul s t] at temp
  simp only [Fintype.card_prod, Fintype.card_coe] at temp
  have h1 : Fintype.card ((s * t : Finset α) : Set α) = Fintype.card (s * t) := by congr
  have h2 :
    ((s : Set α).image (↑) : Set (α ⧸ stabilizer α (s * t))) *
      ((↑) '' (t : Set α) : Set (α ⧸ stabilizer α (s * t))) =
        ((s.image (↑) : Finset (α ⧸ stabilizer α (s * t))) * t.image (↑) :
          Finset (α ⧸ stabilizer α (s * t))) := by simp
  sorry
  -- have h3 :
  --   Fintype.card (((s : Set α).image coe : Set (α ⧸ stabilizer α (s * t))) * coe '' (t : Set α)) =
  --     Fintype.card ((s.image coe : Finset (α ⧸ stabilizer α (s * t))) * image coe t) := by
  --   simp_rw [h2]
  --   congr
  -- simp only [h1, h3, Fintype.card_coe] at temp
  -- rw [temp]

@[to_additive]
lemma subgroup_mul_card_eq_mul_of_mul_stab_subset (s : Subgroup α) (t : Finset α)
    (hst : (s : Set α) ⊆ t.mulStab) :
    Nat.card s * card (t.image (↑) : Finset (α ⧸ s)) = card t := by
  have h : (t : Set α) * s = t := by
    apply Set.Subset.antisymm (Set.Subset.trans (Set.mul_subset_mul_left hst) _)
    · intro x
      rw [Set.mem_mul]
      aesop
    · rw [← coe_mul, mul_mulStab]
  have := s.subgroup_mul_card_eq_mul t
  rw [h] at this
  simpa

@[to_additive]
lemma mul_stab_quotient_commute_subgroup (s : Subgroup α) (t : Finset α)
    (hst : (s : Set α) ⊆ t.mulStab) :
    (t.mulStab.image (↑) : Finset (α ⧸ s)) = (t.image (↑) : Finset (α ⧸ s)).mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have hti : (image (QuotientGroup.mk (s := s)) t).Nonempty := by aesop
  ext x;
  simp only [mem_image, Nonempty.image_iff, mem_mulStab hti]
  constructor
  · rintro ⟨a, hax⟩
    rw [← hax.2]
    ext z
    simp only [mem_smul_finset, mem_image, smul_eq_mul, exists_exists_and_eq_and]
    constructor
    · rintro ⟨b, hbt, hbaz⟩
      use (b * a)
      rw [← mul_mulStab t]
      refine ⟨mul_mem_mul hbt hax.1, ?_⟩
      rw [← hbaz, QuotientGroup.mk_mul, mul_comm]
    · rintro ⟨b, hbt, hbz⟩
      rw [← hbz, ← mul_mulStab t, mul_comm]
      use (a⁻¹ * b)
      refine ⟨mul_mem_mul ?_ hbt, by simp⟩
      rw [← mem_coe, coe_mulStab ht]
      aesop
  · intro hx
    have : s ≤ stabilizer α t := by aesop
    obtain ⟨y, hyx⟩ := Quotient.exists_rep x
    refine ⟨y, (mem_mulStab_iff_subset_smul_finset ht).mpr ?_, by simpa⟩
    intros z hzt
    replace hx : image QuotientGroup.mk (y • t) = image (QuotientGroup.mk (s := s)) t := by
      rw [← hx, ← hyx]
      exact image_smul_comm QuotientGroup.mk y t (congrFun rfl)
    have hyz : QuotientGroup.mk z ∈ image (QuotientGroup.mk (s := s)) (y • t) := by aesop
    simp only [QuotientGroup.mk_mul, mem_image] at hyz
    obtain ⟨a, ha, hayz⟩ := hyz
    obtain ⟨b, hbt, haby⟩ := mem_smul_finset.mp ha
    subst a
    rw [QuotientGroup.eq, smul_eq_mul] at hayz
    replace : ∃ c ∈ mulStab t, (y • b)⁻¹ * z = c := by aesop
    obtain ⟨c, hct, hcbyz⟩ := this
    rw [inv_mul_eq_iff_eq_mul] at hcbyz
    rw [hcbyz, smul_mul_assoc, mul_comm, ← smul_eq_mul]
    exact smul_mem_smul_finset ((mem_mulStab' ht).mp hct hbt)

end Finset
