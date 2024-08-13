import Mathlib.Order.Partition.Finpartition

open Finset Function

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

namespace Finpartition

@[simps]
def finsetImage {a : Finset α} (P : Finpartition a) (f : α → β) (hf : Injective f) :
    Finpartition (a.image f) where
  parts := P.parts.image (image f)
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint, coe_image,
      (image_injective hf).injOn.pairwiseDisjoint_image]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, mem_coe, Function.onFun, Ne,
      Function.id_comp, disjoint_image hf]
    exact P.disjoint
  sup_parts := by
    ext i
    simp only [mem_sup, mem_image, exists_prop, id, exists_exists_and_eq_and]
    constructor
    · rintro ⟨j, hj, i, hij, rfl⟩
      exact ⟨_, P.le hj hij, rfl⟩
    rintro ⟨j, hj, rfl⟩
    rw [← P.sup_parts] at hj
    simp only [mem_sup, id, exists_prop] at hj
    obtain ⟨b, hb, hb'⟩ := hj
    exact ⟨b, hb, _, hb', rfl⟩
  not_bot_mem := by
    simpa only [bot_eq_empty, mem_image, image_eq_empty, exists_prop, exists_eq_right] using
      P.not_bot_mem

def extend' [DistribLattice α] [OrderBot α] {a b c : α} (P : Finpartition a) (hab : Disjoint a b)
    (hc : a ⊔ b = c) : Finpartition c :=
  if hb : b = ⊥ then P.copy (by rw [← hc, hb, sup_bot_eq]) else P.extend hb hab hc

def modPartitions (s d : ℕ) (hd : d ≠ 0) (h : d ≤ s) : Finpartition (range s)
    where
  parts := (range d).image fun i ↦ (range s).filter fun j ↦ j % d = i
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint, coe_image, Set.InjOn.pairwiseDisjoint_image]
    · simp only [Set.PairwiseDisjoint, Function.onFun, Set.Pairwise, mem_coe, mem_range,
        disjoint_left, Function.id_comp, mem_filter, not_and, and_imp]
      rintro x hx y - hxy a - rfl -
      exact hxy
    simp only [Set.InjOn, coe_range, Set.mem_Iio]
    intro x₁ hx₁ x₂ _ h'
    have : x₁ ∈ (range s).filter fun j ↦ j % d = x₂ := by
      rw [← h', mem_filter, mem_range, Nat.mod_eq_of_lt hx₁]
      simp only [hx₁.trans_le h, eq_self_iff_true, and_self_iff]
    rw [mem_filter, Nat.mod_eq_of_lt hx₁] at this
    exact this.2
  sup_parts := by
    rw [sup_image, Function.id_comp]
    refine Subset.antisymm ?_ ?_
    · rw [Finset.sup_eq_biUnion, biUnion_subset]
      simp only [filter_subset, imp_true_iff]
    intro i hi
    have : 0 < d := hd.bot_lt
    simpa [mem_sup, Nat.mod_lt _ this] using hi
  not_bot_mem := by
    simp only [bot_eq_empty, mem_image, mem_range, exists_prop, not_exists, not_and,
      filter_eq_empty_iff, not_forall, Classical.not_not]
    intro i hi
    exact ⟨_, hi.trans_le h, Nat.mod_eq_of_lt hi⟩

lemma modPartitions_parts_eq (s d : ℕ) (hd : d ≠ 0) (h : d ≤ s) :
    (modPartitions s d hd h).parts =
      (range d).image fun i ↦ (range ((s - i - 1) / d + 1)).image fun x ↦ i + d * x := by
  rw [modPartitions]
  ext x
  simp only [mem_image, mem_range]
  refine exists_congr fun i ↦ and_congr_right fun hi ↦ ?_
  suffices
    ((range ((s - i - 1) / d + 1)).image fun x ↦ i + d * x) = (range s).filter fun j ↦ j % d = i
    by rw [this]
  clear x
  ext j
  simp only [mem_image, mem_filter, mem_range, Nat.lt_add_one_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, eq_self_iff_true, and_true_iff, ←
      Nat.lt_sub_iff_add_lt', mul_comm]
    rwa [Nat.le_div_iff_mul_le hd.bot_lt, Nat.le_sub_iff_add_le, Nat.succ_le_iff] at hj
    rw [Nat.succ_le_iff]
    exact Nat.sub_pos_of_lt (hi.trans_le h)
  · rintro ⟨hj, rfl⟩
    refine ⟨j / d, ?_, Nat.mod_add_div _ _⟩
    rwa [Nat.le_div_iff_mul_le' hd.bot_lt, Nat.le_sub_iff_add_le, Nat.le_sub_iff_add_le',
      ← add_assoc, mul_comm, Nat.mod_add_div, Nat.add_one_le_iff]
    · exact hi.le.trans h
    rw [Nat.succ_le_iff]
    exact Nat.sub_pos_of_lt (hi.trans_le h)

end Finpartition
