import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith.Default
import Mathlib.Data.Set.Equitable
import Mathlib.Order.Partition.Equipartition

/-!
# Turan numbers

Since the Turan problem asks for the maximum number of edges in a K_t-free graph of order n, we
don't care about t = 0 or t = 1 so we define turan_num t n to be what most people would call
turan t n, eg turan 0 n is the max size (number of edges) in a K_2 free graph.
Turan's theorem says that this is the number of edges in a balanced complete t-partite graph
-/


open Finset Nat

open scoped BigOperators

namespace Turan

--classical Turan numbers
def turanNum : ℕ → ℕ → ℕ := by
  intro t n
  set a := n / t
  --- size of a small part
  set b := n % t
  -- number of large parts
  exact a ^ 2 * (t - b).choose 2 + a * (a + 1) * b * (t - b) + (a + 1) ^ 2 * b.choose 2

--complement is often easier to deal with and we also multiply by 2 to convert edges to degree sum
-- so 2 * turan_num t n = n ^ 2 - turan_num'  t n
def turanNum' : ℕ → ℕ → ℕ := by
  intro t n
  set a := n / t
  -- size of a small part
  set b := n % t
  -- number of large parts
  exact (t - b) * a ^ 2 + b * (a + 1) ^ 2

-- choose two simplification
theorem two (a : ℕ) : 2 * Nat.choose a 2 = a * (a - 1) := by
  induction' a with a ha; · dsimp; rwa [MulZeroClass.zero_mul, MulZeroClass.mul_zero]
  · rw [Nat.choose, choose_one_right, succ_sub_succ_eq_sub, tsub_zero, mul_add]; norm_num; rw [ha]
    cases eq_zero_or_eq_succ_pred a <;> · rw [h]; ring

-- this is a mess but it works
theorem tn_turanNum' (t n : ℕ) : turanNum' t n + 2 * turanNum t n = n ^ 2 := by
  obtain rfl | ht := @eq_zero_or_pos _ _ t
  · simp only [turan_num, turan_num']
    simp only [zero_add, mod_zero, Nat.div_zero, zero_pow two_pos, sub_zero, MulZeroClass.mul_zero,
      one_pow, mul_one, MulZeroClass.zero_mul, one_mul, two, mul_tsub, sq]
    exact add_tsub_cancel_of_le (le_mul_self _)
  unfold turan_num turan_num'; dsimp
  have n1 := div_add_mod n t
  have n3 : t - n % t + n % t = t := tsub_add_cancel_of_le (mod_lt n ht).le
  set a := n / t with ha
  set b := n % t with hb
  cases' Nat.eq_zero_or_pos n with hn
  · rw [hn] at *
    simp_all only [Nat.zero_div, zero_pow', Ne.def, bit0_eq_zero, Nat.one_ne_zero, not_false_iff,
      MulZeroClass.mul_zero, zero_add, MulZeroClass.zero_mul, choose_zero_succ]
  obtain hb' | hb' := Nat.eq_zero_or_pos b
  · rw [hb'] at *
    rw [add_zero] at n1
    simp only [tsub_zero, add_tsub_cancel_right, MulZeroClass.mul_zero, add_zero,
      MulZeroClass.zero_mul, choose_zero_succ, mul_left_comm 2, two, ← n1]
    ring_nf
    rw [tsub_add_cancel_of_le (succ_le_iff.2 ht)]
    ring
  · rw [← n3, add_mul] at n1 ; nth_rw 3 [← mul_one b] at n1 ; rw [add_assoc, ← mul_add b] at n1
    nth_rw 1 [← n1]; rw [mul_add, mul_add, ← mul_assoc 2, ← mul_assoc 2 ((a + 1) ^ 2)]
    nth_rw 1 [mul_comm 2 _]; nth_rw 2 [mul_comm 2 _]
    rw [mul_assoc, mul_assoc _ 2, two, two, add_sq ((t - b) * a), mul_comm _ (a ^ 2)]
    set c := t - b with hc
    have hc1 : 1 ≤ c := succ_le_iff.2 (tsub_pos_of_lt <| mod_lt n ht)
    have hb1 : 1 ≤ b := by linarith
    have hc2 : c - 1 + 1 = c := by linarith
    have hb2 : b - 1 + 1 = b := by linarith
    ring_nf; rw [hc2, hb2]; nth_rw 4 [← mul_one 2]; rw [← mul_add 2, hb2]; ring_nf

--sum of degrees in a turan graph
theorem tn_turanNum'_2 (t n : ℕ) : 2 * turanNum t n = n ^ 2 - turanNum' t n := by
  rw [← tn_turan_num' t n]
  exact (add_tsub_cancel_left _ _).symm

-- start with some helper functions that don't need partitions to be defined.
-- here P : ℕ → ℕ plays the role of sizes of parts in a t-partition
-- sum of part sizes i.e number of vertices
def psum (t : ℕ) (P : ℕ → ℕ) : ℕ :=
  ∑ i in range t, P i

-- sum of squares of part sizes (basically 2*edges in complement of corresponding complete multipartite graph)
def sumSq (t : ℕ) (P : ℕ → ℕ) : ℕ :=
  ∑ i in range t, P i ^ 2

theorem mod_tplus1 {a b c d t : ℕ} (hc : c < t) (hd : d < t) (h : t * a + c = t * b + d) :
    a = b ∧ c = d := by
  have : c = d := by simpa [mul_comm, mul_add_mod, mod_eq_of_lt, hc, hd] using congr_arg (· % t) h
  simp_all [(zero_le'.trans_lt hc).ne']

--now thinking about balanced t-partitions whose parts sum to n
-- a balanced partition that sums to n
-- def bal (t n : ℕ) (P:ℕ → ℕ) : Prop:= set.equitable_on (range (t + 1) : set ℕ) P ∧ psum t P = n
-- -- given a balanced partition of n into t-parts the small part is n/t and there are n%t large parts
-- lemma bal_sum_n {t n :ℕ} {P :ℕ→ ℕ} (hb: bal t n P) : min_p t P = n/t ∧ (large_parts t P).card = n%t:=
-- begin
--   unfold bal at hb, cases hb with hb1 hb2,
--   rw [bal_sum' hb1, ← div_add_mod n t] at hb2, exact mod_tplus1 (large_parts_card hb1) (le_of_lt_succ (mod_lt n (succ_pos t))) hb2
-- end
-- -- sum of a function f over parts of a balanced partition  of n into t parts is:
-- lemma bal_sum_n_f {t n : ℕ} {P: ℕ → ℕ} (hb: bal t n P)  (f: ℕ → ℕ) :
--  ∑ i in range t, f (P i) = (t+1-n%t) * f(n/t) + (n%t) * f(n/t) :=
-- begin
--   unfold bal at hb,
--   obtain hf :=bal_sum_f hb.1, obtain ⟨mn,ln⟩:= bal_sum_n hb,
--   specialize hf f,
--   rwa [mn, small_parts_card hb.1, ln] at hf,
-- end
-- -- sum of squares of balanced partition is turan_num'
-- lemma bal_turan_help {n t :ℕ} {P:ℕ→ ℕ} (hb: bal t n P):  sum_sq t P = turan_num' t n :=
-- begin
--   rw turan_num' , rw sum_sq, rw bal_sum_n_f hb (λi, i^2),
-- end
-- --so given two balanced t partitions summing to n their sum_sq  agree
-- lemma bal_turan_help' {n t :ℕ} {P Q:ℕ→ ℕ} (hp: bal t n P) (hq: bal t n Q):
--  sum_sq t P = sum_sq t Q:=
-- by rw [bal_turan_help hp, bal_turan_help hq]
-- --hence sum_sq + 2* turan number is n^2
-- lemma bal_turan_bd {n t:ℕ} {P:ℕ→ ℕ} (hp: bal t n P)  : sum_sq t P + 2*turan_num t n = n^2:=
-- begin
--   rw bal_turan_help hp,
--   exact tn_turan_num'  t n,
-- end
--- introduce the partitions we use to build complete multipartite graphs
-- this is a partition of A:finset α into t parts each of which is a finset α
variable {α : Type _} [Fintype α] [Nonempty α] [DecidableEq α] {A : Finset α}

-- --sum of squares of part sizes useful for counting edges in complete multitpartite graph on M
-- def sum_sq_c (P : finpartition A) : ℕ := ∑ i in P.parts, i.card ^ 2
-- -- Any turan partition with M.t and M.A is bal M.t |M.A| ((M.P i).card)
-- lemma turan_bal {P : finpartition A} (hM: P.is_equipartition) : bal M.t M.A.card (λ i, (M.P i).card):=
-- begin
--   rw turan_partition_iff_not_moveable at hM,unfold ¬ P.is_equipartition at hM,
--   rw not_not at hM, rw card_uni, exact ⟨hM,rfl⟩,
-- end
-- -- if v belongs to P i and P j then i = j.
-- lemma uniq_part {P : finpartition A}{v :α} {i j : ℕ} : i ∈ range(M.t)→ j ∈ range(M.t) → v ∈ M.P i → v ∈ M.P j → i = j:=
-- begin
--   intros hi hj hiv hjv, by_contra, have:=M.disj i hi j hj h, exact this (mem_inter.mpr ⟨hiv,hjv⟩)
-- end
-- -- if v belongs to P i and i ≠ j and is in range then v ∉ P j
-- lemma uniq_part' {P : finpartition A}{v :α} {i j : ℕ} : i ∈ range(M.t)→ j ∈ range(M.t) → i ≠ j → v ∈ M.P i → v ∉ M.P j:=
-- begin
--   intros hi hj hiv ne, contrapose hiv,push_neg at hiv,rw not_ne_iff, exact uniq_part hi hj ne hiv
-- end
-- -- every part is contained in A
-- lemma sub_part {M:finpartition A} {i : ℕ} (hi: i ∈ range(M.t)) : M.P i ⊆ M.A :=
-- begin
--   rw M.uni, intros x hx,  rw  mem_bUnion,  exact ⟨i,hi,hx⟩
-- end
-- -- if there are two different parts then the sum of their sizes is at most the size of the whole
-- -- could make a version for any number of parts ≥ 2 but don't need it,
-- lemma two_parts {P : finpartition A} {i j : ℕ} (hi: i ∈ range(M.t))  (hj: j ∈ range(M.t)) (hne: i≠ j) : (M.P i).card + (M.P j).card ≤ M.A.card:=
-- begin
--   rw card_uni, rw ← sum_erase_add (range(M.t)) _ hj, apply nat.add_le_add_right,
--   rw ← sum_erase_add ((range(M.t)).erase j) _ (mem_erase_of_ne_of_mem hne hi),
--   nth_rewrite 0 ← zero_add (M.P i).card, apply nat.add_le_add_right,
--   simp only [zero_le]
-- end
-- --A is the union of each part and the sdiff
-- lemma sdiff_part {M:finpartition A} {i : ℕ} (hi: i ∈ range(M.t)) : M.A = M.A\(M.P i)∪M.P i :=
-- begin
--   have:= sub_part hi,
--   rwa [sdiff_union_self_eq_union, left_eq_union_iff_subset] at *,
-- end
-- -- each part is disjoint from its sdiff with the whole
-- lemma disjoint_part {M:finpartition A} {i : ℕ} : disjoint ((M.A)\(M.P i)) (M.P i) := sdiff_disjoint
-- -- size of uni = sum of rest and part
-- lemma card_part_uni {M:finpartition A} {i : ℕ} (hi: i ∈ range(M.t)):  M.A.card= (M.A\(M.P i)).card + (M.P i).card:=
-- begin
--   nth_rewrite 0 sdiff_part hi,
--   apply card_disjoint_union sdiff_disjoint
-- end
-- --  We can create a new partition by moving v ∈ M.P i from P i to P j.
-- -- We only want to do this if this increases the number of edges in the complete multipartite graph.
-- --  Any non-Turan partition contains a vertex that can be moved to increase
-- --  the number of edges in corresponding graph
-- -- TODO: figure out why "(M.P j).insert v" caused an error (so used (M.P j)∪ {v} instead)
-- --  but it didn't complain about "(M.P i).erase v"
-- --- Error message :'insert' is not a valid "field" because environment does not contain
-- -- 'finset.insert' M.P j which has type finset α
-- --- This is due to the "insert" defined for finpartition A above that clashes, and somehow finset.insert doesn't work
-- def move (P : finpartition A) {v : α} {i j: ℕ} (hvi: i∈ range(M.t) ∧ v∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) : finpartition A :={
--   t:=M.t,
--   P:= begin intros k, exact ite (k ≠ i ∧ k ≠ j) (M.P k) (ite (k = i) ((M.P i).erase v) ((M.P j) ∪ {v})),end,
--   A:=M.A,
--   uni:=begin
--     rw M.uni,ext,split, {rw [mem_bUnion,mem_bUnion],intros h,simp only [*, mem_range, ne.def, exists_prop] at *,
--     by_cases hav: a=v,{
--       refine ⟨j,hj.1,_⟩,rw ← hav at *, split_ifs,{exfalso, exact h_1.2 rfl},{exfalso, push_neg at h_1,exact hj.2 h_2},
--       {refine mem_union_right _ (mem_singleton_self a)}, },
--       {obtain ⟨k,hk1,hk2⟩:=h,
--       refine ⟨k,hk1,_⟩, split_ifs, {exact hk2}, {refine mem_erase.mpr _,rw h_1 at hk2, exact ⟨hav,hk2⟩},
--       {push_neg at h, rw (h h_1) at hk2, exact mem_union_left _ hk2},},},
--     {rw [mem_bUnion,mem_bUnion],intros h,simp only [*, mem_range, ne.def, exists_prop] at *,
--     by_cases hav: a=v,{
--       rw ← hav at hvi, exact ⟨ i,hvi⟩},
--       {obtain ⟨k,hk1,hk2⟩:=h, split_ifs at hk2, {exact ⟨k,hk1,hk2⟩}, {exact ⟨i,hvi.1,(erase_subset v (M.P i)) hk2⟩},
--       {refine ⟨j,hj.1,_⟩, rw mem_union at hk2, cases hk2, {exact hk2},{exfalso, exact hav (mem_singleton.mp hk2)},},},}, end,
--   disj:=begin
--     intros a ha b hb ne,split_ifs, {exact M.disj a ha b hb ne},
--     {have:=M.disj a ha i hvi.1 h.1, apply disjoint_of_subset_right _ this, exact erase_subset _ _},
--     {simp only [disjoint_union_right, disjoint_singleton_right], refine ⟨M.disj a ha j hj.1 h.2,_⟩,
--     intro hv, exact h.1 (uniq_part ha hvi.1 hv hvi.2)},
--     {have:=M.disj i hvi.1 b hb  h_2.1.symm,apply disjoint_of_subset_left _ this, exact erase_subset _ _},
--     {exfalso, push_neg at h, push_neg at h_2,rw [h_1,h_3] at ne, exact ne rfl},
--     {simp only [disjoint_union_right, disjoint_singleton_right, mem_erase, _root_.ne.def, eq_self_iff_true, not_true, false_and,
--     not_false_iff, and_true],
--     have:=M.disj i hvi.1 j hj.1 hj.2.symm, apply disjoint_of_subset_left _ this, exact erase_subset _ _},
--     {simp only [disjoint_union_left, disjoint_singleton_right],
--     refine ⟨M.disj j hj.1 b hb h_2.2.symm,_⟩, rw disjoint_singleton_left,
--     intro hb2, have:= uniq_part hb hvi.1 hb2 hvi.2 , exact h_2.1 this},
--     {simp only [disjoint_union_left, disjoint_singleton_left, mem_erase, _root_.ne.def, eq_self_iff_true],
--     simp only [not_true, false_and,not_false_iff, and_true],
--     have:=M.disj j hj.1  i hvi.1 hj.2, apply disjoint_of_subset_right _ this, exact erase_subset _ _},
--     {exfalso, push_neg at h_2,push_neg at h, have bj:= h_2 h_3, have aj:= h h_1,rw aj at ne, rw bj at ne, exact ne rfl},
-- end,}
-- -- new whole is same as old
-- lemma move_A {P : finpartition A} {v : α} {i j: ℕ} (hvi: i∈ range(M.t) ∧ v∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) :(move M hvi hj).A=M.A:=
-- rfl
-- -- the moved partition still has t parts
-- lemma move_t {P : finpartition A} {v : α} {i j: ℕ} (hvi: i∈ range(M.t) ∧ v∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) :(move M hvi hj).t=M.t:=
--  rfl
-- -- the moved parts are the same except for P i and P j which have lost/gained v
-- lemma move_P {P : finpartition A} {v : α} {i j k: ℕ} (hvi: i∈ range(M.t) ∧ v∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) : k∈ range(M.t) → ((move M hvi hj).P k) = ite (k≠i ∧k≠j) (M.P k) (ite (k=i) ((M.P i).erase v) ((M.P j) ∪ {v})):=
-- begin
--   intros k , refl,
-- end
-- -- the sizes of parts changed by moving v
-- lemma move_Pcard {P : finpartition A} {v : α} {i j k: ℕ} (hvi: i∈ range(M.t) ∧ v∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) : k∈ range(M.t) → ((move M hvi hj).P k).card = ite (k≠i ∧k≠j) (M.P k).card (ite (k=i) ((M.P i).card -1) ((M.P j).card+1)):=
-- begin
--   intros hk,rw move_P hvi hj hk,split_ifs,
--   {refl},  {exact card_erase_of_mem hvi.2},{
--   have jv:=uniq_part' hvi.1 hj.1 hj.2.symm hvi.2,
--   rw ← disjoint_singleton_right at jv,
--   apply card_disjoint_union jv}
-- end
-- --- the complement of the part with v has gained v
-- lemma sdiff_erase {v : α} {A B :finset α} (hB: B⊆A) (hv: v ∈ B) : A\(B.erase v)=(A\B) ∪ {v} :=
-- begin
--   ext, split, {intro h, rw [mem_union,mem_sdiff] at *,rw mem_sdiff at h,rw mem_erase at h,
--   push_neg at h, by_cases h': a=v,{right, exact mem_singleton.mpr h'},
--   {left, exact ⟨h.1,(h.2 h')⟩}},
--   {intros h,rw mem_sdiff,rw mem_erase,rw [mem_union,mem_sdiff] at h, push_neg,
--   cases h,{exact ⟨h.1,λi,h.2⟩},{by_contra h',push_neg at h',
--   have ha:=hB hv,
--   have:=mem_singleton.mp h, rw ← this at ha,
--   have h2:=h' ha, exact h2.1 this},}
-- end
-- --..hence its size  has increased
-- lemma card_sdiff_erase {v : α} {A B :finset α} (hB: B⊆A) (hv: v ∈ B) : (A\(B.erase v)).card=(A\B).card+1 :=
-- begin
--   have hv2: v∉A\B, {rw mem_sdiff,push_neg,intro i, exact hv,},
--   have:=disjoint_singleton_right.mpr hv2,
--   rw sdiff_erase hB hv, exact card_disjoint_union this
-- end
-- --  complement of part without v has lost v
-- lemma sdiff_insert {v : α} {A B :finset α} (hB: B⊆A) (hv: v ∉ B) : A\(B ∪  {v})=(A\B).erase v:=
-- begin
--   ext,split,{intro h,
--   rw mem_erase, rw mem_sdiff at *,rw mem_union at h, push_neg at h,rw mem_singleton at h,  exact ⟨h.2.2,h.1,h.2.1⟩},
--   {intro h,rw mem_erase at h, rw mem_sdiff, rw mem_union, push_neg,rw mem_singleton, rw mem_sdiff at h, exact ⟨h.2.1,h.2.2,h.1⟩}
-- end
-- --- .. hence its size has decreased
-- lemma card_sdiff_insert {v : α} {A B :finset α} (hB: B⊆A) (hvB: v ∉ B) (hvA: v ∈ A) : (A\(B ∪ {v})).card=(A\B).card -1:=
-- begin
--   have : v∈A\B:=mem_sdiff.mpr ⟨hvA,hvB⟩,
--   rw sdiff_insert hB hvB, exact card_erase_of_mem this
-- end
-- -- how have the sizes of the complements of parts changed by moving v
-- -- for parts other than i and j nothing has changed, for i and j we have calculated the changes above
-- lemma move_Pcard_sdiff {P : finpartition A} {v : α} {i j k: ℕ} (hvi: i∈ range(M.t) ∧ v∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) :
--  k∈ range(M.t) → (((move M hvi hj).A)\((move M hvi hj).P k)).card = ite (k≠i ∧k≠j) ((M.A)\(M.P k)).card (ite (k=i) (((M.A)\(M.P i)).card +1) (((M.A)\(M.P j)).card-1)):=
-- begin
--   intros hk,rw move_P hvi hj hk,rw move_A hvi hj,split_ifs, {refl},
--   {exact card_sdiff_erase (sub_part  hvi.1) hvi.2},
--   {exact card_sdiff_insert (sub_part  hj.1) (uniq_part' hvi.1 hj.1 hj.2.symm hvi.2) (mem_part hvi.1 hvi.2)}
-- end
-- -- key increment inequality we need to show moving a vertex in a ¬ P.is_equipartition partition is increases deg sum
-- -- (TODO: rewrite this now I'm not a complete novice..)
-- lemma move_change {a b n:ℕ} (hb: b+1<a) (hn: a+b ≤ n):  a*(n-a) +b*(n-b) < (a-1)*(n-a+1)+ (b+1)*(n-b-1):=
-- begin
--   rw mul_add, rw add_mul,rw mul_one, rw one_mul,
--   have ha:=tsub_add_cancel_of_le (by linarith [hb]: 1 ≤ a),
--   have h2: a ≤ n-b:=le_tsub_of_add_le_right hn,
--   have hnb:=tsub_add_cancel_of_le  (le_trans (by linarith [hb]: 1 ≤ a) h2),
--   nth_rewrite 0 ← ha, nth_rewrite 0 ← hnb,
--   rw [add_mul,mul_add,one_mul,mul_one ,add_assoc,add_assoc],
--   apply nat.add_lt_add_left,
--   rw [add_comm, ← add_assoc, add_comm (a-1), add_assoc, add_assoc],
--   apply nat.add_lt_add_left,
--   have ab: b< a-1:=by linarith [hb],
--   have nba: (n-a)< (n-b-1),{
--     have nba': (n-a)<(n-(b+1)),{
--       have h3:=tsub_pos_of_lt hb,
--       have h4: a ≤ n :=by linarith,
--       have h6:=tsub_add_tsub_cancel (h4) (le_of_lt hb),
--       linarith,}, rw add_comm at nba',
--       rwa tsub_add_eq_tsub_tsub_swap at nba',},
--   exact nat.add_lt_add ab nba
-- end
end Turan
