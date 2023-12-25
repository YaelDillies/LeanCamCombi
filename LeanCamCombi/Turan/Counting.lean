import Mathlib.Combinatorics.SimpleGraph.Degree
import Turan.Number
import Turan.Induced

#align_import turan.counting

open Finset Nat Turan

open scoped BigOperators

namespace SimpleGraph

variable {t n : ℕ}

variable {α : Type _} (G H : SimpleGraph α) [Fintype α] [Nonempty α] [DecidableEq α]
  [DecidableRel G.Adj] [DecidableRel H.Adj] {A : Finset α}

-- ---for any (t+2)-clique free set there is a partition into B, a t-clique free set and A\B
-- -- such that e(A)+e(A\B) ≤ e(B) + |B|(|A|-|B|)
-- lemma fueredi_help (ht : t ≠ 0) (hA : G.clique_free_on A (t + 1)) :
--   ∃ B, B ⊆ A ∧ G.clique_free_on B t ∧
--     ∑ v in A, G.deg_on A v + ∑ v in A \ B, G.deg_on (A \ B) v
--       ≤ ∑ v in B, G.deg_on B v + 2 * B.card * (A \ B).card :=
-- begin
--   obtain _ | _ | t := t,
--   { cases ht rfl },
--   ----- t = 1 need to check that ∅ is not a 1-clique.
--   { haveI : is_refl α G.adjᶜ := ⟨G.loopless⟩,
--     refine ⟨∅, empty_subset A, G.clique_free_on_empty.2 $ by norm_num, _⟩,
--     simpa [deg_on, eq_empty_iff_forall_not_mem, set.pairwise_iff_of_refl] using hA },
-- ----- 1 < t case
--   obtain rfl | hnem := A.eq_empty_or_nonempty,
--   { refine ⟨∅, subset.rfl, G.clique_free_on_empty.2 ht, _⟩,
--     simp },
--   obtain ⟨x, hxA, hxM⟩:=G.exists_max_res_deg_vertex hnem, -- get a vert x of max res deg in A
--   set hBA := G.sub_res_nbhd_A x A,
--   set B := (A ∩ G.neighbor_finset x) with hB,-- Let B be the res nbhd of the vertex x of max deg_A
--   refine ⟨B, ⟨hBA,(G.t_clique_free hA hxA),_⟩⟩,
--   rw [G.deg_on_add_sum hBA, G.sum_sdf hBA B, add_assoc],
--   rw [G.sum_sdf hBA (A\B),G.sum_deg_on_comm hBA,← G.deg_on_add_sum hBA ],
--   rw ← hB, rw ← add_assoc, ring_nf,
--   apply add_le_add_left _ (∑ v in B, G.deg_on v B ),
--   rw add_comm, rw add_assoc, nth_rewrite 1 add_comm,
--   rw ← G.deg_on_add_sum hBA, ring_nf,rw mul_assoc,
--   refine mul_le_mul' (by norm_num) _,
--   apply le_trans (G.max_deg_on_sum_le (sdiff_subset A B)) _,
--   rw [hxM,deg_on],
-- end
-- -- Putting together the deg counts of G induced on a larger partition (M with C inserted).
-- -- Counting degrees sums over the parts of the larger partition is what you expect
-- -- ie e(G[M_0])+ .. +e(G[M_t])+e(G[C]) = e(G[M'_0])+...+e(G[M'_{t}])
-- lemma internal_count {P : finpartition A} {C : finset α} (h: disjoint M.A C):
--  ∑ i in range(M.t),∑ v in (M.P i), G.deg_on v (M.P i) + ∑ v in C, G.deg_on v C  =
-- ∑ i in range((insert M h).t), ∑ v in ((insert M h).P i), G.deg_on v ((insert M h).P i):=
-- begin
--   simp [insert_t, insert_P,ite_not],
--   have  ru:range((M.t)+1)=range(M.t) ∪ {M.t},{
--     rw range_succ, rw union_comm, rw insert_eq _,},
--   have nm:(M.t)∉(range(M.t)):=not_mem_range_self,
--   have rd: disjoint (range(M.t)) {M.t}:= disjoint_singleton_right.mpr nm,
--   rw [ru,sum_union rd],simp only [sum_singleton, eq_self_iff_true, if_true],
--   apply (add_left_inj _).mpr, apply sum_congr rfl, intros k hk,
--   have nm:(M.t)∉(range(M.t)):=not_mem_range_self,
--   have kne: k≠M.t,{intro h',rw h' at hk, exact nm hk},
--   apply sum_congr, split_ifs,{contradiction},{refl},{
--   intros v hv,split_ifs,{contradiction},{refl}},
-- end
-- -- Füredi's stability theorem: (t+2)-clique-free set A implies there is a t-partition of A
-- -- such that edges in A + edges in parts (counted a second time) ≤ edges in the complete
-- -- t-partite graph on same partition
-- -- implies Turan once we know how to maximize edges of a complete multi-partite graph
-- theorem fueredi : ∀A:finset α, G.clique_free_on A (t+2) → ∃M:finpartition A, M.A=A ∧ M.t =t ∧
-- ∑v in A, G.deg_on A v + ∑ i in range(M.t),∑ v in (M.P i), G.deg_on v (M.P i) ≤ ∑ v in A, (mp M).deg_on A v:=
-- begin
--   induction t with t ht, {rw zero_add,
--   intros A ha, use (default_M A 0), refine ⟨rfl,rfl,_⟩, rw G.two_clique_free_sum ha,
--   rw zero_add, unfold default_M, dsimp,simp, apply sum_le_sum,
--   intros x hx, rw G.clique_free_on_two ha x hx,exact zero_le _ },
--   --- t.succ case
--   {intros A ha, obtain⟨B,hBa,hBc,hBs⟩:=G.fueredi_help A ha,
--   have hAsd:=union_sdiff_of_subset hBa,
--   obtain ⟨M,Ma,Mt,Ms⟩:=ht B hBc,
--   have dAB:disjoint M.A (A\B), {rw Ma, exact disjoint_sdiff,},
--   set H: simple_graph α:= (mp (insert M dAB)),
--   use (insert M dAB), refine ⟨_,_,_⟩,{
--   rw [insert_AB, Ma], exact union_sdiff_of_subset hBa}, {rwa [insert_t, Mt]},{
--   --- so we now have the new partition and "just" need to check the degree sum bound..
--   have mpc:=mp_count M dAB, rw [insert_AB, Ma , hAsd] at mpc,
--   -- need to sort out the sum over parts in the larger graph
--   rw ←  mpc, rw ← G.internal_count dAB, linarith},},
-- end
end SimpleGraph

