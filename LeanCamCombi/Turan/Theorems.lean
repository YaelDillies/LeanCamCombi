import Turan.Counting

#align_import turan.theorems

/-!
# Füredi stability result (no counting)

If G is K_{t+2}-free with vertex set α then there is a t-partition M of α
 such that the e(G)+ ∑ i< t, e(G[M_i]) ≤ e(complete_multipartite M)

# Turan's theorem

Together with an upper bound on the number of edges in any complete multipartite graph
Füredi's result easily implies Turan with equality iff G is a complete multipartite graph on a
turan partition (ie. a Turan graph)

def turan_num : ℕ → ℕ → ℕ:=
begin
  intros t n,
  set a:= n/t,--- size of a small part
  set b:= n%t,-- number of large parts
  exact (a^2)*nat.choose(t+1-b)(2)+a*(a+1)*b*(t+1-b)+((a+1)^2)*nat.choose(b)(2)
end

#eval turan_num 1 11  -- = 5*6 = 30        K_3-free bipartite
#eval turan_num 2 12  -- = 3*(4*4) = 48    K_4-free tri-partite
#eval turan_num 5 23  -- = 5*(4*3) +(5 choose 2)*(4*4) = 60+160 = 220 --  K_7-free 6-partite

# Füredi with counting

If G is K_{t+2}-free and is close to extremal in size then G is close to t-partite.
-/


open Finset Nat Turan

open scoped BigOperators

namespace SimpleGraph

variable {t n : ℕ}

variable {α : Type _} (G H : SimpleGraph α) [Fintype α] [Nonempty α] {s : Finset α} [DecidableEq α]
  [DecidableRel G.Adj] [DecidableRel H.Adj]

-- theorem fueredi_stability : G.clique_free (t+2) → ∃ P : finpartition A, M.t = t ∧ M.A = univ ∧
-- G.edge_finset.card + ∑ i in range t, (G.ind (M.P i)).edge_finset.card ≤ (mp M).edge_finset.card:=
-- begin
--   intro h, obtain ⟨M,hA,ht,hs⟩:=G.fueredi univ (G.clique_free_graph_imp_set h),
--   refine ⟨M,ht,hA,_⟩,apply (mul_le_mul_left (by norm_num:0<2)).mp, rw [mul_add, mul_sum], simp only [deg_on_univ] at hs,
--   rw  [← G.sum_degrees_eq_twice_card_edges,← (mp M).sum_degrees_eq_twice_card_edges],
--   apply le_trans _ hs, apply add_le_add_left, apply le_of_eq, apply sum_congr, rwa ht,
--   intros i hi, rw ← ind_edge_count,
-- end
-- -- So we have e(G)+edges internal to the partiton ≤ edges of complete t-partite M
-- theorem fueredi_stability' : G.clique_free (t+2) → ∃ P : finpartition A, M.t=t ∧ M.A=univ ∧
-- G.edge_finset.card + (G.disJoin M).edge_finset.card ≤ (mp M).edge_finset.card:=
-- begin
--   intro h, obtain⟨M,ht,hu,hle⟩:=G.fueredi_stability h, rw ← ht at hle,rw ← G.disJoin_edge_sum hu at hle,
--   exact ⟨M,ht,hu,hle⟩,
-- end
-- --Now deduce Turan's theorem without worring about case of equality yet
-- theorem turan : G.clique_free (t+2) → G.edge_finset.card ≤ turan_num t (fintype.card α):=
-- begin
--   intro h, obtain ⟨M,ht,hA,hc⟩:=G.fueredi_stability h,
--   have :=turan_max_edges M hA,rw ht at this,
--   apply le_trans (le_of_add_le_left hc) this,
-- end
-- -- Uniqueness?
-- ---There are three places where G can fail to achieve equality in Füredi's stability theorem
-- -- 1) there are "internal" edges, ie edges inside a part of the t-partition  (counted in the LHS)
-- -- 2) the partition can fail to be balanced (and hence #edgesof mp M < turan_num)
-- -- 3) the multipartite induced graph G ⊓ (mp M) may not be complete
-- -- Clearly for equality in Füredi-Turan hybrid ie LHS of Füredi with RHS of Turan
-- -- need M is a balanced partition and G is multipartite (ie no internal edges)
-- -- can then prove in this case G ≤ (mp M) = T and hence G = T for equality.
-- --Now deduce case of equality in Turan's theorem
-- theorem turan_equality :
--    G.clique_free (t+2) ∧ G.edge_finset.card = turan_num t (fintype.card α)
--  ↔  ∃ M:finpartition A, M.t=t ∧ M.A=univ ∧ P.is_equipartition ∧ G = mp M:=
-- begin
--   split,{
--   intro h,obtain ⟨M,ht,hu,hle⟩:=G.fueredi_stability' h.1, rw h.2 at hle,
--   refine ⟨M,ht,hu,_⟩, have tm:=turan_max_edges M hu, rw ht at tm,
--   have inz:(G.disJoin M).edge_finset.card=0:= by linarith, rw card_eq_zero at inz,
--   have inem: (G.disJoin M)=⊥:=empty_iff_edge_empty.mpr inz,
--   have dec:=G.self_eq_disJoin_ext_mp hu,rw inem at dec, simp only [bot_sup_eq, left_eq_inf] at dec,
--   have ieq:(mp M).edge_finset.card= turan_num t (fintype.card α):=by linarith, rw ← ht at ieq,
--   refine ⟨turan_eq_imp M hu ieq,_⟩, rw ←  h.2 at tm,
--   exact edge_finset_inj.1 (eq_of_subset_of_card_le (edge_finset_subset_edge_finset.2 hs) hc)
--   exact edge_eq_sub_imp_eq dec tm},
--   { intro h, obtain ⟨M,ht,hu,iM,hG⟩:=h,
--     have hc:=mp_clique_free M ht hu,
--     have ieq:=turan_imm_imp_eq M hu ht iM,  rw ← hG at hc,
--     refine ⟨hc,_⟩,
-- --    rw ← hG at ieq, ---TO DO: figure out why this rewrite of "G = mp M" doesn't work ... "motive is not type correct"
--     rw ← ieq,
--     simp_rw hG }
-- end
-- -- The usual version of Füredi's stability theorem says:
-- -- if G is (K_t+2)-free and has (turan numb - s) edges
-- -- then we can make G t-partite by deleting at most s edges
-- theorem fueredi_stability_count {s : ℕ} : G.clique_free (t+2) → G.edge_finset.card = turan_num t (fintype.card α) - s →
-- ∃ P : finpartition A, M.t=t ∧ M.A=univ  ∧ G.is_close (mp M) s:=
-- begin
-- --
-- intros h1 h2, obtain ⟨M,ht,hA,hle⟩:=G.fueredi_stability' h1,
-- refine ⟨M,ht,hA,_⟩, rw h2 at hle,
-- have tm:=turan_max_edges M hA, rw  ht at tm,
-- by_cases hs: s≤ turan_num t (fintype.card α),{
-- have ic:(G.disJoin M).edge_finset.card ≤ s:= by linarith,
-- have id:=G.self_eq_disJoin_ext_mp hA,
-- refine ⟨(G.disJoin M).edge_finset,_,ic⟩,
-- rw G.del_fedges_is_sdiff (G.disJoin M),{ rw G.sdiff_with_int hA,
--   by { intro, simp { contextual := tt } },},
--   {exact (G.disJoin M).edge_finset},},
--   {have :G.edge_finset.card ≤s:=by linarith,
--     exact G.is_close_trivial (mp M) s (this)},
-- end
end SimpleGraph

