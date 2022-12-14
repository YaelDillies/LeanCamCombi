/-
Copyright (c) 2022 YaÃ«l Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YaÃ«l Dillies
-/
import analysis.normed_space.hahn_banach.extension
import combinatorics.double_counting
import order.partition.finpartition

/-!
# The Littlewood-Offord problem

-/

open_locale big_operators

namespace finset
variables {Î¹ E : Type*} [normed_add_comm_group E] [normed_space â E] {ð : finset (finset Î¹)}
  {s : finset Î¹} {f : Î¹ â E} {r : â}

lemma exists_littlewood_offord_partition [decidable_eq Î¹] (hr : 0 < r) (hf : â i â s, r â¤ âf iâ) :
  â P : finpartition s.powerset,
    P.parts.card = s.card.choose (s.card / 2) â§
    (â (ð â P.parts) (t â ð), t â s) â§
    (â ð â P.parts,
      (ð : set (finset Î¹)).pairwise $ Î» u v, r â¤ dist (â i in u, f i) (â i in v, f i)) :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { exact â¨finpartition.indiscrete $ singleton_ne_empty _, by simpâ© },
  obtain â¨P, hP, hs, hPrâ© := ih (Î» j hj, hf _ $ mem_insert_of_mem hj),
  clear ih,
  obtain â¨g, hg, hgfâ© := exists_dual_vector â (f i)
    (norm_pos_iff.1 $ hr.trans_le $ hf _ $ mem_insert_self _ _),
  choose t ht using Î» ð (hð : ð â P.parts),
    finset.exists_max_image _ (Î» t, g (â i in t, f i)) (P.nonempty_of_mem_parts hð),
  sorry,
end

/-- **Kleitman's theorem** -/
lemma card_le_of_forall_dist_sum_le (hr : 0 < r) (hð : â t â ð, t â s) (hf : â i â s, r â¤ âf iâ)
  (hðr : â u v â ð, dist (â i in u, f i) (â i in v, f i) < r) :
  ð.card â¤ s.card.choose (s.card / 2) :=
begin
  classical,
  obtain â¨P, hP, hs, hrâ© := exists_littlewood_offord_partition hr hf,
  rw âhP,
  refine card_le_card_of_forall_subsingleton (â) (Î» t ht, _)
    (Î» â¬ hâ¬ t ht u hu, (hr _ hâ¬).eq ht.2 hu.2 (hðr _ ht.1 _ hu.1).not_le),
  simpa only [exists_prop] using P.exists_mem (mem_powerset.2 $ hð _ ht),
end

end finset
