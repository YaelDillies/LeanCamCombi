/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.normed_space.hahn_banach.extension
import combinatorics.double_counting
import order.partition.finpartition

/-!
# The Littlewood-Offord problem

-/

open_locale big_operators

namespace finset
variables {ι E : Type*} [normed_add_comm_group E] [normed_space ℝ E] {𝒜 : finset (finset ι)}
  {s : finset ι} {f : ι → E} {r : ℝ}

lemma exists_littlewood_offord_partition [decidable_eq ι] (hr : 0 < r) (hf : ∀ i ∈ s, r ≤ ‖f i‖) :
  ∃ P : finpartition s.powerset,
    P.parts.card = s.card.choose (s.card / 2) ∧
    (∀ (𝒜 ∈ P.parts) (t ∈ 𝒜), t ⊆ s) ∧
    (∀ 𝒜 ∈ P.parts,
      (𝒜 : set (finset ι)).pairwise $ λ u v, r ≤ dist (∑ i in u, f i) (∑ i in v, f i)) :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { exact ⟨finpartition.indiscrete $ singleton_ne_empty _, by simp⟩ },
  obtain ⟨P, hP, hs, hPr⟩ := ih (λ j hj, hf _ $ mem_insert_of_mem hj),
  clear ih,
  obtain ⟨g, hg, hgf⟩ := exists_dual_vector ℝ (f i)
    (norm_pos_iff.1 $ hr.trans_le $ hf _ $ mem_insert_self _ _),
  choose t ht using λ 𝒜 (h𝒜 : 𝒜 ∈ P.parts),
    finset.exists_max_image _ (λ t, g (∑ i in t, f i)) (P.nonempty_of_mem_parts h𝒜),
  sorry,
end

/-- **Kleitman's theorem** -/
lemma card_le_of_forall_dist_sum_le (hr : 0 < r) (h𝒜 : ∀ t ∈ 𝒜, t ⊆ s) (hf : ∀ i ∈ s, r ≤ ‖f i‖)
  (h𝒜r : ∀ u v ∈ 𝒜, dist (∑ i in u, f i) (∑ i in v, f i) < r) :
  𝒜.card ≤ s.card.choose (s.card / 2) :=
begin
  classical,
  obtain ⟨P, hP, hs, hr⟩ := exists_littlewood_offord_partition hr hf,
  rw ←hP,
  refine card_le_card_of_forall_subsingleton (∈) (λ t ht, _)
    (λ ℬ hℬ t ht u hu, (hr _ hℬ).eq ht.2 hu.2 (h𝒜r _ ht.1 _ hu.1).not_le),
  simpa only [exists_prop] using P.exists_mem (mem_powerset.2 $ h𝒜 _ ht),
end

end finset
