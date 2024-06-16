/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Order.Partition.Finpartition
import LeanCamCombi.Combinatorics.Chap1.Sec1.SCD

/-!
# Symmetric Decompositions into Sparse Sets

The Littlewood-Offord problem
-/

open scoped BigOperators

namespace Finset
variable {α E : Type*} {𝒜 : Finset (Finset α)}
  {s : Finset α} {f : α → E} {r : ℝ}

def profile (𝒜 : Finset (Finset α)) : Multiset ℕ := sorry

def subpartition (f : ):

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_littlewood_offord_partition [DecidableEq α] (hr : 0 < r) (hf : ∀ i ∈ s, r ≤ ‖f i‖) :
    ∃ P : Finpartition s.powerset,
      P.parts.card = s.card.choose (s.card / 2) ∧
        (∀ 𝒜 ∈ P.parts, ∀ t ∈ 𝒜, t ⊆ s) ∧
          ∀ 𝒜 ∈ P.parts,
            (𝒜 : Set (Finset α)).Pairwise fun u v ↦ r ≤ dist (∑ i in u, f i) (∑ i in v, f i) := by
  classical
  induction' s using Finset.induction with i s hi ih
  · exact ⟨Finpartition.indiscrete $ singleton_ne_empty _, by simp⟩
  obtain ⟨P, hP, hs, hPr⟩ := ih fun j hj ↦ hf _ $ mem_insert_of_mem hj
  clear ih
  obtain ⟨g, hg, hgf⟩ :=
    exists_dual_vector ℝ (f i) (norm_pos_iff.1 $ hr.trans_le $ hf _ $ mem_insert_self _ _)
  choose t ht using fun 𝒜 (h𝒜 : 𝒜 ∈ P.parts) ↦
    Finset.exists_max_image _ (fun t ↦ g (∑ i in t, f i)) (P.nonempty_of_mem_parts h𝒜)
  sorry

/-- **Kleitman's lemma** -/
lemma card_le_of_forall_dist_sum_le (hr : 0 < r) (h𝒜 : ∀ t ∈ 𝒜, t ⊆ s) (hf : ∀ i ∈ s, r ≤ ‖f i‖)
    (h𝒜r : ∀ u, u ∈ 𝒜 → ∀ v, v ∈ 𝒜 → dist (∑ i in u, f i) (∑ i in v, f i) < r) :
    𝒜.card ≤ s.card.choose (s.card / 2) := by
  classical
  obtain ⟨P, hP, _hs, hr⟩ := exists_littlewood_offord_partition hr hf
  rw [← hP]
  refine'
    card_le_card_of_forall_subsingleton (· ∈ ·) (fun t ht ↦ _) fun ℬ hℬ t ht u hu ↦
      (hr _ hℬ).eq ht.2 hu.2 (h𝒜r _ ht.1 _ hu.1).not_le
  simpa only [exists_prop] using P.exists_mem (mem_powerset.2 $ h𝒜 _ ht)

end Finset
