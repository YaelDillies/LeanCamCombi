/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Tactic.NthRewrite

/-!
# Lines in the plane and decompositions of graphs : Sylvester-Gallai

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 11: "Pigeon-hole and double counting".
In this file, we formalize the Sylvester-Gallai theorem.


## Structure

- `Sylvester_Gallai` :
      Among any finite set of points not all on a line,
      we may find 2 of them such that no other point of
      the set is on the line they span.

- `Sylvester_Gallai_condition_fact` :
      It turns out that the condition that the points aren't
      aligned implies that there's at least 3 points.

- `line` :
      We use a home-made definition of a line, and show a bunch
      of its properties, relating to membership, rewriting,
      nonemptyness, convexity, and completeness, the latter
      of which uses a `sorry`. Sorry.

- `pigeons_on_a_line` :
      Is the argument for why one part of the line cut along
      the projection will conatin two of 3 points.
      It's used in the proof of `Sylvester_Gallai`, and it
      makes use of the pigeonhole principle.

- `point_line_finset` :
      The pairs of points and lines, so that the point isn't
      on the line, and the line is spanned by two points of
      the point set.

- `point_line_proj` :
      Defines the projection of a point on a `line`.

- `min_dist` :
      Is the minimum distance among the point-line pairs
      of `point_line_finset`.

-/

open Finset

-- We'll work in a real Hilbert space (complete inner product space with dot-product in ℝ)
-- As you may check from the docstring of `InnerProductSpace`, we require `NormedAddCommGroup`.
variable {E : Type} [_inst_1 : NormedAddCommGroup E] [_inst_2 : InnerProductSpace ℝ E]
  [_inst_3 : CompleteSpace E]

/-- The line passing through `a` and `b`, as a set.
Note: when `a=b` this is a point.
-/
def line (a b : E) : Set E :=
  {x : E | ∃ t : ℝ, x = a + t • (b - a)}

@[simp] lemma left_mem_line (a b : E) : a ∈ line a b := ⟨0, by simp⟩
@[simp] lemma right_mem_line (a b : E) : b ∈ line a b := ⟨1, by simp⟩

lemma line_nonempty (a b : E) : (line a b).Nonempty := ⟨a, left_mem_line _ _⟩

/-- A rewrite lemma -/
theorem line_comm (a b : E) : line a b = line b a := by
  rw [line, line]
  ext x
  constructor
  · rintro ⟨tx, xdef⟩
    use 1 - tx
    rw [sub_smul]
    rw [one_smul]
    rw [add_sub]
    rw [add_sub_cancel'_right]
    rw [show a - b = -(b - a) by rw [neg_sub]]
    rw [smul_neg]
    rwa [sub_neg_eq_add]
  · rintro ⟨tx, xdef⟩
    use 1 - tx
    rw [sub_smul]
    rw [one_smul]
    rw [add_sub]
    rw [add_sub_cancel'_right]
    rw [show b - a = -(a - b) by rw [neg_sub]]
    rw [smul_neg]
    rwa [sub_neg_eq_add]

/-- Lines are complete.
We need this to define projections in `point_line_proj`.
-/
theorem line_complete {a b : E} : IsComplete (line a b) := by
  apply (IsSeqClosed.isClosed _).isComplete
  intro x y hx hy
  choose t ht using hx
  -- This is how far I'll go.
  sorry

/-- Lines are convex.
We need this to define projections in `point_line_proj`.
-/
theorem line_convex {x y : E} : Convex ℝ (line x y) := by
  rintro _ ⟨t, rfl⟩ _ ⟨u, rfl⟩ a b _ _ hab
  refine ⟨a * t + b * u, ?_⟩
  simp_rw [smul_add, add_add_add_comm, Convex.combo_self hab, ← mul_smul, ← add_smul]

/-- A rewrite lemma -/
theorem line_rw_of_mem {a b c : E} (h : c ∈ line a b) : line a b = line c (c + (b - a)) := by
  rw [line, line]
  rw [line] at h
  cases' h with tc cdef
  ext x
  constructor
  · rintro ⟨tx, xdef⟩
    use tx - tc
    rw [cdef]
    rw [add_sub_cancel']
    rw [add_assoc]
    rw [← add_smul]
    rw [add_sub]
    rw [add_sub_cancel']
    exact xdef
  · rintro ⟨tx, xdef⟩
    rw [add_sub_cancel'] at xdef
    rw [cdef] at xdef
    rw [add_assoc, ← add_smul] at xdef
    use tc + tx

/-- A rewrite lemma -/
theorem line_rw_of_mem_of_mem {a b c d : E} (hcd : c ≠ d) (hc : c ∈ line a b) (hd : d ∈ line a b) :
    line a b = line c d := by
  rw [line] at *
  rw [line]
  cases' hc with tc cdef
  cases' hd with td ddef
  ext x
  constructor
  · rintro ⟨tx, xdef⟩
    have : td - tc ≠ 0 := by
      by_contra con
      rw [sub_eq_zero] at con
      apply hcd
      rw [cdef, ddef, con]
    use(tx - tc) / (td - tc)
    rw [cdef, ddef]
    simp only [add_sub_add_left_eq_sub]
    rw [← sub_smul]
    rw [smul_smul]
    rw [div_mul_cancel _ this]
    rw [add_assoc]
    rw [← add_smul]
    rw [add_sub]
    rw [add_sub_cancel']
    exact xdef
  · rintro ⟨tx, xdef⟩
    rw [cdef, ddef] at xdef
    simp only [add_sub_add_left_eq_sub] at xdef
    rw [← sub_smul] at xdef
    rw [smul_smul] at xdef
    rw [add_assoc] at xdef
    rw [← add_smul] at xdef
    use tc + tx * (td - tc)

/-- For 3 distinct points `a,b,c` on a line, and a 4th point `p`
on the line, we may find 2 distinct points `x,y` among `a,b,c`,
so that `p` and `y` are on the same side of the line wrt. `x`,
and in fact `y` is on the segment [x,p].
-/
theorem pigeons_on_a_line {a b c p : E} (hc : c ∈ line a b) (hp : p ∈ line a b) (hab : a ≠ b)
    (hac : a ≠ c) (hcb : c ≠ b) :
    ∃ x,
      (x = a ∨ x = b ∨ x = c) ∧
        ∃ y, (y = a ∨ y = b ∨ y = c) ∧ y ≠ x ∧ ∃ t : ℝ, (0 < t ∧ t ≤ 1) ∧ y = x + t • (p - x) := by
  have ha := left_mem_line a b
  have hb := right_mem_line a b
  -- We "center" the line at `p`
  rw [line_rw_of_mem hp] at ha hb hc
  cases' ha with ta adef
  cases' hb with tb bdef
  cases' hc with tc cdef
  rw [add_sub_cancel'] at *
  /-
    We cut the line into two sides delimited by `p`,
    The pigeonhole principle says that 2 of the three points
    `a,b,c` must be on a common side of `p`.
    -/
  -- The pigeonhole map
  let f := fun t : ℝ => if ht : 0 ≤ t then 1 else 0
  -- The size condition
  have cond_1 : ({0, 1} : Finset ℕ).card < ({ta, tb, tc} : Finset ℝ).card := by
    have : ta ∉ ({tb, tc} : Finset ℝ) := by
      rw [mem_insert, mem_singleton]
      rintro (rfl | rfl)
      · apply hab
        rw [adef]
        nth_rw 2 [bdef]
      apply hac
      rw [adef, cdef]
    nth_rw 1 [card_insert_of_not_mem this]
    clear this
    have : tb ∉ ({tc} : Finset ℝ) := by
      rw [mem_singleton]
      rintro rfl
      apply hcb
      rw [bdef, cdef]
    nth_rw 1 [card_insert_of_not_mem this]
    simp only [card_doubleton, lt_add_iff_pos_right, eq_self_iff_true, Nat.lt_one_iff,
      card_singleton]
    decide
  --The mapping condition
  have cond_2 : ∀ x, x ∈ ({ta, tb, tc} : Finset ℝ) → f x ∈ ({0, 1} : Finset ℕ) := by
    intro x _
    rw [mem_insert]
    rw [mem_singleton]
    dsimp [f]
    by_cases q : 0 ≤ x
    rw [if_pos q]
    right
    rfl
    rw [if_neg q]
    left
    rfl
  -- We apply the pigeonhole principle
  obtain ⟨u, udef, v, vdef, unv, same⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to cond_1 cond_2
  clear cond_1 cond_2
  dsimp [f] at same
  -- We simplify "same"
  have signz : 0 ≤ u ∧ 0 ≤ v ∨ u < 0 ∧ v < 0 := by
    obtain h | h := le_or_lt 0 u
    rw [if_pos h] at same
    rw [eq_comm] at same
    rw [Ne.ite_eq_left_iff Nat.one_ne_zero] at same
    left; exact ⟨h, same⟩
    rw [lt_iff_not_le] at h
    rw [if_neg h] at same
    rw [eq_comm] at same
    rw [Ne.ite_eq_right_iff Nat.one_ne_zero] at same
    rw [← lt_iff_not_le] at h
    rw [← lt_iff_not_le] at same
    right; exact ⟨h, same⟩
  clear same
  --wlog W : (0≤u ∧ 0≤v), --fails
  have tec :
    ∀ x,
      x ∈ ({ta, tb, tc} : Finset ℝ) →
        p + x • (b - a) = a ∨ p + x • (b - a) = b ∨ p + x • (b - a) = c := by
    intro x xdef
    rw [mem_insert, mem_insert, mem_singleton] at xdef
    obtain rfl | rfl | rfl := xdef
    rw [← adef]
    left; rfl
    rw [← bdef]
    right; left; rfl
    rw [← cdef]
    right; right; rfl
  obtain signz | signz := signz
  · --wlog H : v < u with Sym, --fails
    apply ltByCases v u
    · intro vltu
      use p + u • (b - a)
      constructor
      · exact tec u udef
      use p + v • (b - a)
      constructor
      · exact tec v vdef
      constructor
      · intro con
        rw [add_right_inj] at con
        rw [← sub_eq_zero] at con
        rw [← sub_smul] at con
        rw [smul_eq_zero] at con
        obtain con | con := con
        rw [sub_eq_zero] at con
        rw [con] at vltu
        exact (lt_irrefl u) vltu
        rw [sub_eq_zero] at con
        exact hab con.symm
      · use (u - v) / u
        have : u ≠ 0 := by
          rintro rfl
          exact signz.2.not_lt vltu
        constructor
        · constructor
          rw [div_pos_iff]
          left
          constructor
          rw [sub_pos]
          exact vltu
          apply lt_of_le_of_ne signz.1 (Ne.symm this)
          rw [div_le_iff (lt_of_le_of_ne signz.1 (Ne.symm this))]
          rw [one_mul]
          apply sub_le_self
          exact signz.2
        · rw [sub_add_cancel']
          rw [← neg_smul]
          rw [smul_smul]
          rw [add_assoc]
          rw [← add_smul]
          rw [mul_neg]
          rw [div_mul_cancel _ this]
          rw [neg_sub]
          rw [add_sub]
          rw [add_sub_cancel']
    · intro problem
      exfalso
      exact unv problem.symm
    -- same, with u and v swapped
    · intro vltu
      use p + v • (b - a)
      constructor
      · exact tec v vdef
      use p + u • (b - a)
      constructor
      · exact tec u udef
      constructor
      · intro con
        rw [add_right_inj] at con
        rw [← sub_eq_zero] at con
        rw [← sub_smul] at con
        rw [smul_eq_zero] at con
        obtain con | con := con
        rw [sub_eq_zero] at con
        rw [con] at vltu
        exact (lt_irrefl v) vltu
        rw [sub_eq_zero] at con
        exact hab con.symm
      · use(v - u) / v
        have : v ≠ 0 := by
          intro con
          apply lt_irrefl (0 : ℝ)
          rw [con] at vltu
          exact lt_of_le_of_lt signz.1 vltu
        constructor
        · constructor
          rw [div_pos_iff]
          left
          constructor
          rw [sub_pos]
          exact vltu
          apply lt_of_le_of_ne signz.2 (Ne.symm this)
          rw [div_le_iff (lt_of_le_of_ne signz.2 (Ne.symm this))]
          rw [one_mul]
          apply sub_le_self
          exact signz.1
        · rw [sub_add_cancel']
          rw [← neg_smul]
          rw [smul_smul]
          rw [add_assoc]
          rw [← add_smul]
          rw [mul_neg]
          rw [div_mul_cancel _ this]
          rw [neg_sub]
          rw [add_sub]
          rw [add_sub_cancel']
  -- Negative u and v
  -- There are some minor changes in the proof
  · apply ltByCases v u
    · intro vltu
      use p + v • (b - a)
      constructor
      · exact tec v vdef
      use p + u • (b - a)
      constructor
      · exact tec u udef
      constructor
      · intro con
        rw [add_right_inj] at con
        rw [← sub_eq_zero] at con
        rw [← sub_smul] at con
        rw [smul_eq_zero] at con
        obtain con | con := con
        rw [sub_eq_zero] at con
        rw [con] at vltu
        exact (lt_irrefl v) vltu
        rw [sub_eq_zero] at con
        exact hab con.symm
      · use(v - u) / v
        have : v ≠ 0 := ne_of_lt signz.2
        constructor
        · constructor
          rw [div_pos_iff]
          right
          constructor
          rw [sub_neg]
          exact vltu
          exact signz.2
          rw [div_le_iff_of_neg signz.2]
          rw [one_mul]
          rw [le_sub_self_iff]
          exact le_of_lt signz.1
        · rw [sub_add_cancel']
          rw [← neg_smul]
          rw [smul_smul]
          rw [add_assoc]
          rw [← add_smul]
          rw [mul_neg]
          rw [div_mul_cancel _ this]
          rw [neg_sub]
          rw [add_sub]
          rw [add_sub_cancel']
    · intro problem
      exfalso
      exact unv problem.symm
    -- same, with u and v swapped
    · intro vltu
      use p + u • (b - a)
      constructor
      · exact tec u udef
      use p + v • (b - a)
      constructor
      · exact tec v vdef
      constructor
      · intro con
        rw [add_right_inj] at con
        rw [← sub_eq_zero] at con
        rw [← sub_smul] at con
        rw [smul_eq_zero] at con
        obtain con | con := con
        rw [sub_eq_zero] at con
        rw [con] at vltu
        exact (lt_irrefl u) vltu
        rw [sub_eq_zero] at con
        exact hab con.symm
      · use(u - v) / u
        have : u ≠ 0 := ne_of_lt signz.1
        constructor
        · constructor
          rw [div_pos_iff]
          right
          constructor
          rw [sub_neg]
          exact vltu
          exact signz.1
          rw [div_le_iff_of_neg signz.1]
          rw [one_mul]
          rw [le_sub_self_iff]
          exact le_of_lt signz.2
        · rw [sub_add_cancel']
          rw [← neg_smul]
          rw [smul_smul]
          rw [add_assoc]
          rw [← add_smul]
          rw [mul_neg]
          rw [div_mul_cancel _ this]
          rw [neg_sub]
          rw [add_sub]
          rw [add_sub_cancel']

open scoped Classical

-- due to decidability of a point belonging to a line or not
/-- For a finite set of points `P`, we consider the set of pairs
of points of `P` and lines through points of `P`, so that
the point isn't on the line.

This is modeled by represetning a line by its two points of `P`,
asking fro this triple of points to be distinct and finally asking
the first point to not be on the line spanned by the two others.
-/
noncomputable def pointLineFinset (P : Finset E) :=
  (univ : Finset (↥P × ↥P × ↥P)).filter fun (a, b, c) ↦
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a.val ∉ line b.val c.val

/-- We obtain two distinct points from a set of size at least 2.
Compare to `finset.card_eq_two` for sets of size 2.
-/
theorem pair_of_2_le_card {α : Type} {s : Finset α} (h : 2 ≤ s.card) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  have first : 0 < s.card := by linarith
  rw [card_pos] at first
  obtain ⟨fst, fst_def⟩ := first
  use fst
  have second : 0 < (s.erase fst).card := by
    have := card_erase_add_one fst_def
    rw [← this] at h
    linarith
  rw [card_pos] at second
  obtain ⟨snd, snd_def⟩ := second
  use snd
  constructor; exact fst_def
  constructor; apply (erase_subset fst s) snd_def
  intro con
  rw [← con] at snd_def
  exact (not_mem_erase fst s) snd_def

-- I initially proved this, but it turns out that the pair was fine,
-- I'm keeping it here as it may be mathlib material.
theorem triple_of_3_le_card {α : Type} {s : Finset α} (h : 3 ≤ s.card) :
    ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ c ≠ b := by
  have first : 0 < s.card := by linarith
  rw [card_pos] at first
  obtain ⟨fst, fst_def⟩ := first
  use fst
  have second : 0 < (s.erase fst).card := by
    have := card_erase_add_one fst_def
    rw [← this] at h
    linarith
  rw [card_pos] at second
  obtain ⟨snd, snd_def⟩ := second
  use snd
  have third : 0 < ((s.erase fst).erase snd).card := by
    have := card_erase_add_one fst_def
    have that := @card_erase_add_one _ (s.erase fst) snd _ snd_def
    rw [← this] at h
    linarith
  rw [card_pos] at third
  obtain ⟨thr, thr_def⟩ : _ := third
  use thr
  constructor; exact fst_def
  constructor; apply (erase_subset fst s) snd_def
  constructor;
  apply
    (Subset.trans (erase_subset snd (s.erase fst)) (erase_subset fst s))
      thr_def
  constructor
  intro con
  rw [← con] at snd_def
  apply (not_mem_erase fst s) snd_def
  constructor
  intro con
  rw [← con] at thr_def
  rw [mem_erase] at thr_def
  apply (not_mem_erase fst s) thr_def.2
  intro con
  rw [← con] at thr_def
  apply (not_mem_erase thr (s.erase fst)) thr_def

/-- I turns out that the condition that the points of `P`
aren't aligned implies that `P` has at least 3 points.
-/
theorem Sylvester_Gallai_condition_fact (P : Finset E) (hSG : ¬∃ a b : E, ∀ p ∈ P, p ∈ line a b) :
    3 ≤ P.card := by
  by_contra! con
  interval_cases hP : P.card
  -- If there are no points, the ∀ statement of `hSG` is true.
  · rw [card_eq_zero] at hP
    apply hSG
    use 0; use 0
    intro p problem
    exfalso
    rw [hP] at problem
    exact (not_mem_empty p) problem
  -- If there's one point, all points are on any line containing that point
  · rw [card_eq_one] at hP
    cases' hP with e hP
    apply hSG
    use e; use e
    intro p pdef
    rw [hP] at pdef
    rw [mem_singleton] at pdef
    rw [pdef]
    apply left_mem_line
  -- If there are two points, all points are on the line they span
  · rw [card_eq_two] at hP
    rcases hP with ⟨a, b, -, hP⟩
    apply hSG
    use a; use b
    simp [hP]

/-- Seeing as the "general position" implies that we have 3 points,
it also implies that the point-line-pairs set is non-empty.

We need this to define the minimum distance of points to lines
in `min_dist`.
-/
theorem pointLineFinset_nonempty (P : Finset E) (hSG : ¬∃ a b : E, ∀ p ∈ P, p ∈ line a b) :
    (pointLineFinset P).Nonempty := by
  have hP := Sylvester_Gallai_condition_fact P hSG
  by_contra! con
  simp only [not_nonempty_iff_eq_empty, pointLineFinset] at con
  obtain ⟨a, b, aP, bP, anb⟩ := pair_of_2_le_card (show 2 ≤ P.card by linarith)
  rw [filter_eq_empty_iff] at con
  specialize con
  simp at con
  apply hSG
  use a; use b
  intro p pdef
  specialize con p pdef a aP b bP
  by_cases q1 : p = a
  · rw [q1]; apply left_mem_line
  by_cases q2 : p = b
  · rw [q2]; apply right_mem_line
  · rw [Ne.def] at anb
    exact con q1 q2 anb

/-- For a triple of points, we define the projection of the first
on the line spanned by the two others.
-/
noncomputable def pointLineProj (P : Finset E) (hSG : ¬∃ a b : E, ∀ p ∈ P, p ∈ line a b)
    (t : ↥P × ↥P × ↥P) :=
  Classical.choose
    (@exists_norm_eq_iInf_of_complete_convex _ _ _
      (-- By projection, we mean distance minimiser
        line
        t.2.1.val t.2.2.val)
      (by apply line_nonempty) (by apply line_complete) (by apply line_convex) t.1.val)

/-- The property of the projection `point_line_proj`:
it's on the line that the first point was projected on,
and it minimises the distance to that first point,
among points on the line.
-/
theorem point_line_dist_def (P : Finset E) (hSG : ¬∃ a b : E, ∀ p ∈ P, p ∈ line a b)
    (t : ↥P × ↥P × ↥P) :
    pointLineProj P hSG t ∈ line t.2.1.val t.2.2.val ∧
      ‖t.1.val - pointLineProj P hSG t‖ = ⨅ w : ↥(line t.2.1.val t.2.2.val), ‖t.1.val - ↑w‖ := by
  rw [pointLineProj]
  exact
    Classical.choose_spec
      (@exists_norm_eq_iInf_of_complete_convex _ _ _ (line t.2.1.val t.2.2.val)
        (by apply line_nonempty) (by apply line_complete) (by apply line_convex) t.1.val)

/-- We consider the minimum distance of a point to a line,
where the point and the line form a triple of the
point-line-pair set `point_line_finset` we defined.
-/
noncomputable def minDist (P : Finset E) (hSG : ¬∃ a b : E, ∀ p ∈ P, p ∈ line a b) :=
  min'
    (image (fun t : ↥P × ↥P × ↥P => ‖↑t.1 - pointLineProj P hSG t‖)
      (-- `.val` raises an error.
        pointLineFinset
        P))
    (by
      apply Nonempty.image
      exact pointLineFinset_nonempty P hSG)

/-- A geometric lemma to handle a case of the
the proof-by-picture of `Sylvester_Gallai`.
-/
theorem SG_Thales_like (x y z r t : E) (s : ℝ) (hs : 0 < s ∧ s < 1) (hy : y = x + s • (z - x))
    (hr : r = x + s • (t - x)) (htz : z ≠ t) : ‖y - r‖ < ‖z - t‖ := by
  rw [hy, hr]
  simp only [add_sub_add_left_eq_sub]
  rw [← smul_sub]
  rw [sub_sub_sub_cancel_right]
  rw [norm_smul]
  rw [Real.norm_of_nonneg (le_of_lt hs.1)]
  nth_rw 2 [← one_mul ‖z - t‖]
  apply mul_lt_mul
  exact hs.2
  rfl
  rw [norm_sub_pos_iff]
  exact htz
  exact zero_le_one

/-- A geometric lemma to handle a case of the
the proof-by-picture of `Sylvester_Gallai`.
-/
theorem SG_Pythagoras_workaround (x y z p t : E) (hyz : y = z) (htz : t ≠ z)
    (izptp : inner (z - p) (t - p) ≤ (0 : ℝ)) (iypxp : inner (y - p) (x - p) ≤ (0 : ℝ))
    (itzxz : inner (t - z) (x - z) ≤ (0 : ℝ)) : ‖y - p‖ < ‖z - t‖ := by
  subst y
  have : ‖z - p‖ * ‖z - p‖ + ‖t - p‖ * ‖t - p‖ ≤ ‖z - t‖ * ‖z - t‖ := by
    rw [← zero_add (‖z - t‖ * ‖z - t‖)]
    rw [← sub_le_iff_le_add]
    rw [show z - t = z - p - (t - p) by
        simp only [eq_self_iff_true, sub_sub_sub_cancel_right, sub_left_inj]]
    rw [← MulZeroClass.zero_mul (2 : ℝ)]
    rw [← div_le_iff _]
    rw [← real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    exact izptp
    norm_num
  by_contra! con
  obtain rfl : t = p := by simpa [← sq, (sq_nonneg _).le_iff_eq, sub_eq_zero]
    using this.trans $ mul_self_le_mul_self (norm_nonneg _) con
  have := this.trans $ mul_self_le_mul_self (norm_nonneg _) con
  rw [← inner_neg_neg, neg_sub, neg_sub] at itzxz
  have := add_nonpos itzxz iypxp
  -- have problem : z = p := by
  --   rw [← sub_eq_zero]
  --   rw [← norm_eq_zero]
  --   rw [← sq_eq_zero_iff]
  --   apply le_antisymm
  --   swap
  --   apply sq_nonneg
  --   rw [show ‖z - p‖ ^ 2 = ↑(‖z - p‖ ^ 2 : ℝ) by
  --       simp only [IsROrC.ofReal_real_eq_id, id.def, eq_self_iff_true, sq_eq_sq]]
  --   push_cast
  --   rw [← @inner_self_eq_norm_sq_to_K ℝ _ _ _ _ (z - p)]
  --   nth_rw 2 [show z - p = z - x + (x - p) by
  --       simp only [eq_self_iff_true, sub_add_sub_cancel, sub_left_inj]]
  --   rw [inner_add_right]
  --   exact add_nonpos itzxz iypxp
  -- rw [← problem] at eq
  -- exact htz Eq

/-- ### The Sylvester-Gallai theorem:

Among any finite set of points not all on a line,
we may find 2 of them such that no other point of
the set is on the line they span.
-/

theorem Sylvester_Gallai (P : Finset E) (hSG : ¬∃ a b : E, ∀ p ∈ P, p ∈ line a b) :
    ∃ a ∈ P, ∃ ∈ P, a ≠ b ∧ ∀ p ∈ P, p ≠ a → p ≠ b → p ∉ line a b := by
  /-
    We consider the minimum distance of the first of a triple of points
    to the line spanned by the other two, where the points are distinct,
    and the first isn't on the line spanned by the other two
    -/
  set d := minDist P hSG with d_def
  rw [minDist] at d_def
  have d_prop :=
    min'_mem
      (image (fun t : ↥P × ↥P × ↥P => ‖↑t.1 - pointLineProj P hSG t‖) (pointLineFinset P))
      (by
        apply Nonempty.image
        exact pointLineFinset_nonempty P hSG)
  rw [← d_def] at d_prop
  rw [mem_image] at d_prop
  rcases d_prop with ⟨t, tdef, tdist⟩
  -- The two points from this minimum achieving line satisfy the result
  use t.2.1.val
  constructor; exact t.2.1.Prop
  use t.2.2.val
  constructor; exact t.2.2.Prop
  -- We prove this by contradiction
  by_contra! con
  rw [pointLineFinset] at tdef
  rw [mem_filter] at tdef
  specialize con _
  · intro K
    apply tdef.2.2.2.1
    exact Subtype.eq K
  -- Hence, we assume there's a third point `q` on the line
  rcases con with ⟨q, qP, qnt21, qnt22, qline⟩
  obtain ⟨proj_mem, proj_prop⟩ := point_line_dist_def P hSG t
  -- We locate the projection wrt. the three points on the line
  obtain ⟨x, xdef, y, ydef, ynx, s, s_prop, yxs⟩ :=
    pigeons_on_a_line qline proj_mem (by intro con; apply tdef.2.2.2.1; exact Subtype.eq con)
      (Ne.symm qnt21) qnt22
  /-
    We consider the point-line-pair made of the point bewteen
    the projection and another point of the line, and the new line
    spanned by that other point, and the initially projected point.
    We'll use this triple contradict minimailty of `d`.
    -/
  set t' :=
    ((⟨y, by
          cases ydef; rw [ydef]; exact t.2.1.Prop
          cases ydef; rw [ydef]; exact t.2.2.Prop
          rw [ydef]; exact qP⟩ :
        ↥P),
      ((⟨x, by
            cases xdef; rw [xdef]; exact t.2.1.Prop
            cases xdef; rw [xdef]; exact t.2.2.Prop
            rw [xdef]; exact qP⟩ :
          ↥P),
        t.1)) with
    t'_def
  -- The properties of the projection from that new triple
  obtain ⟨proj_mem', proj_prop'⟩ := point_line_dist_def P hSG t'
  simp_rw [t'_def] at proj_prop'
  simp_rw [t'_def] at proj_mem'
  have yline : y ∉ line x t.fst.val := by
    have : x ∈ line t.2.1.val t.2.2.val := by
      cases xdef; rw [xdef]; apply left_mem_line
      cases xdef; rw [xdef]; apply right_mem_line
      rw [xdef]; exact qline
    have that : y ∈ line t.2.1.val t.2.2.val := by
      cases ydef; rw [ydef]; apply left_mem_line
      cases ydef; rw [ydef]; apply right_mem_line
      rw [ydef]; exact qline
    intro thot
    have line_eq : line t.2.1.val t.2.2.val = line x t.1.val := by
      have := line_rw_of_mem_of_mem (Ne.symm ynx) this that
      rw [this]; clear this
      have := line_rw_of_mem_of_mem (Ne.symm ynx) (@left_mem_line _ _ _ _ x t.1.val) thot
      rw [this]
    apply tdef.2.2.2.2
    rw [line_eq]
    apply right_mem_line
  -- We consider the parallel to the first projection segement,
  -- passing through `y`, with a more adequate definition:
  set r := x + s • (t.1.val - x) with r_def
  by_cases Qs : s = 1
  -- The case where `y = p`, and we use `SG_Pythagoras_workaround`.
  · rw [Qs, one_smul, add_sub_cancel'_right] at yxs
    rw [Qs, one_smul, add_sub_cancel'_right] at r_def
    have :=
      SG_Pythagoras_workaround x y (pointLineProj P hSG t) (pointLineProj P hSG t') t.1.val yxs
        (by
          rw [← yxs]
          cases ydef; rw [ydef]; intro con; apply tdef.2.1; exact Subtype.eq con
          cases ydef; rw [ydef]; intro con; apply tdef.2.2.1; exact Subtype.eq con
          rw [yxs]
          intro con
          apply tdef.2.2.2.2
          rw [con]
          exact proj_mem)
        (by
          have :=
            (@norm_eq_iInf_iff_real_inner_le_zero _ _ _ _ line_convex) (pointLineProj P hSG t) _
              proj_mem'
          rw [← yxs] at this ; rw [← yxs]
          apply this.mp proj_prop'
          apply right_mem_line)
        (by
          have := (@norm_eq_iInf_iff_real_inner_le_zero _ _ _ _ line_convex) y _ proj_mem'
          rw [t'_def]
          apply this.mp proj_prop'
          apply left_mem_line)
        (by
          have := (@norm_eq_iInf_iff_real_inner_le_zero _ _ _ _ line_convex) t.1.val _ proj_mem
          apply this.mp proj_prop
          cases xdef; rw [xdef]; apply left_mem_line
          cases xdef; rw [xdef]; apply right_mem_line
          rw [xdef]; exact qline)
    -- We have therefor found a smaller distance
    nth_rw 2 [norm_sub_rev] at this
    rw [Subtype.val_eq_coe] at this
    rw [tdist] at this
    -- We'll derive the contradiction from minimality
    apply not_le_of_lt this
    rw [d_def]
    apply min'_le
    -- From here on, we need to do some justifications for why
    -- the supposed smaller distance is part of the set of distances
    rw [mem_image]
    use t'
    constructor
    · rw [t'_def, pointLineFinset]
      simp only [true_and_iff, mem_univ, Subtype.mk_eq_mk, mem_filter, Subtype.coe_mk]
      constructor
      intro con; apply ynx; simpa using con
      constructor
      intro con
      replace con : y = t.1.val := by rw [← con]
      rw [con] at ydef
      cases' ydef with cy cy; apply tdef.2.1; exact Subtype.eq cy
      cases' cy with cy cy; apply tdef.2.2.1; exact Subtype.eq cy
      rw [← cy] at qline ; exact tdef.2.2.2.2 qline
      constructor
      intro con
      replace con : x = t.1.val := by rw [← con]
      rw [con] at xdef
      cases' xdef with cy cy; apply tdef.2.1; exact Subtype.eq cy
      cases' cy with cy cy; apply tdef.2.2.1; exact Subtype.eq cy
      rw [← cy] at qline ; exact tdef.2.2.2.2 qline
      exact yline
    simp only [t'_def, eq_self_iff_true, Subtype.coe_mk]
  -- The case where `y ≠p`, where we use `SG_Thales_like` .
  · replace Qs := lt_of_le_of_ne s_prop.2 Qs
    have :=
      SG_Thales_like x y (pointLineProj P hSG t) r t.1.val s ⟨s_prop.1, Qs⟩ yxs r_def
        (by
          intro con
          apply tdef.2.2.2.2
          rw [← con]
          exact proj_mem)
    -- We've again found a smaller distance
    nth_rw 2 [norm_sub_rev] at this
    rw [Subtype.val_eq_coe] at this
    rw [tdist] at this
    -- We must relate it to distance from the set
    have transition : ‖y - pointLineProj P hSG t'‖ ≤ ‖y - r‖ := by
      rw [t'_def]
      rw [proj_prop']
      have r_mem : r ∈ line t'.2.1.val t'.2.2.val := by
        simp [t'_def]
        use s
        rw [← Subtype.val_eq_coe]
      apply
        @ciInf_le _ _ _ (fun w : ↥(line t'.snd.fst.val t'.snd.snd.val) => ‖y - ↑w‖) _
          (⟨r, r_mem⟩ : ↥(line t'.snd.fst.val t'.snd.snd.val))
      -- Thanks Yael !
      use(0 : ℝ)
      rw [mem_lowerBounds]
      intro norm normdef
      rw [Set.mem_range] at normdef
      cases' normdef with point pointdist
      rw [← pointdist]
      apply norm_nonneg
    -- Minimality requires:
    have problem : d ≤ ‖y - pointLineProj P hSG t'‖ := by
      rw [d_def]
      apply min'_le
      rw [mem_image]
      use t'
      constructor
      · simp only [true_and_iff, pointLineFinset.equations._eqn_1, mem_univ,
          Subtype.mk_eq_mk, mem_filter, Subtype.coe_mk]
        constructor
        intro con; apply ynx; simpa using con
        constructor
        intro con
        replace con : y = t.1.val := by rw [← con]
        rw [con] at ydef
        cases' ydef with cy cy; apply tdef.2.1; exact Subtype.eq cy
        cases' cy with cy cy; apply tdef.2.2.1; exact Subtype.eq cy
        rw [← cy] at qline ; exact tdef.2.2.2.2 qline
        constructor
        intro con
        replace con : x = t.1.val := by rw [← con]
        rw [con] at xdef
        cases' xdef with cy cy; apply tdef.2.1; exact Subtype.eq cy
        cases' cy with cy cy; apply tdef.2.2.1; exact Subtype.eq cy
        rw [← cy] at qline ; exact tdef.2.2.2.2 qline
        exact yline
      · simp only [t'_def, eq_self_iff_true, Subtype.coe_mk]
    -- We reach the desired contradction
    apply lt_irrefl d
    exact lt_of_le_of_lt (le_trans problem transition) this
