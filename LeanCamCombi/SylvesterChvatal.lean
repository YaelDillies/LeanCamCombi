import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Finite.List
import LeanCamCombi.MetricBetween

variable {V : Type*} [MetricSpace V]

section
variable {u v w : V}

open scoped MetricBetweenness

@[mk_iff]
inductive Set.collinearTriple : Set V → Prop
| mk {u v w : V} (h : sbtw u v w) : collinearTriple {u, v, w}

-- lemma Finset.collinearTriple_iff {}
inductive GenerateLine (s : Set V) : Set V
| basic {x : V} : x ∈ s → GenerateLine s x
| extend_out (u v w : V) : GenerateLine s u → GenerateLine s v → sbtw u v w → GenerateLine s w
| extend_in (u v w : V) : GenerateLine s u → GenerateLine s v → sbtw u w v → GenerateLine s w

lemma subset_generateLine (s : Set V) : s ⊆ GenerateLine s := fun _ => GenerateLine.basic

lemma generateLine_close_right {s : Set V} {x y z : V}
  (hx : x ∈ GenerateLine s) (hy : y ∈ GenerateLine s)
  (h : sbtw x y z) : z ∈ GenerateLine s := GenerateLine.extend_out x y _ hx hy h

lemma generateLine_close_left {s : Set V} {x y z : V}
  (hx : x ∈ GenerateLine s) (hy : y ∈ GenerateLine s)
  (h : sbtw z x y) : z ∈ GenerateLine s := GenerateLine.extend_out y x _ hy hx h.symm

lemma generateLine_close_middle {s : Set V} {x y z : V}
  (hx : x ∈ GenerateLine s) (hy : y ∈ GenerateLine s)
  (h : sbtw x z y) : z ∈ GenerateLine s := GenerateLine.extend_in _ _ _ hx hy h

lemma generateLine_minimal {S L : Set V} (hL₀ : S ⊆ L)
    (out_closed : ∀ {x y z}, x ∈ L → y ∈ L → sbtw x y z → z ∈ L)
    (in_closed : ∀ {x y z}, x ∈ L → y ∈ L → sbtw x z y → z ∈ L) :
    GenerateLine S ⊆ L := by
  intro x hx
  induction hx with
  | basic h => exact hL₀ h
  | extend_out u v w _ _ hw hu hv => exact out_closed hu hv hw
  | extend_in u v w _ _ hw hu hv => exact in_closed hu hv hw

def Line (a b : V) : Set V := GenerateLine ({a, b} : Set V)

@[simp] lemma left_mem_Line {a b : V} : a ∈ Line a b := subset_generateLine _ (by simp)
@[simp] lemma right_mem_Line {a b : V} : b ∈ Line a b := subset_generateLine _ (by simp)
lemma left_extend_mem_Line {a b c : V} (h : sbtw c a b) : c ∈ Line a b :=
  generateLine_close_left left_mem_Line right_mem_Line h
lemma middle_extend_mem_Line {a b c : V} (h : sbtw a c b) : c ∈ Line a b :=
  generateLine_close_middle left_mem_Line right_mem_Line h
lemma right_extend_mem_Line {a b c : V} (h : sbtw a b c) : c ∈ Line a b :=
  generateLine_close_right left_mem_Line right_mem_Line h

lemma Line_comm : Line u v = Line v u := by rw [Line, Line, Set.pair_comm]

def Set.IsLine (l : Set V) : Prop := ∃ a b, a ≠ b ∧ Line a b = l

lemma Line_isLine {a b : V} (h : a ≠ b) : (Line a b).IsLine := ⟨a, b, h, rfl⟩

lemma Set.IsLine.close_right {L : Set V} (hL : L.IsLine) {a b c : V} (ha : a ∈ L) (hb : b ∈ L)
    (hc : sbtw a b c) : c ∈ L := by
  obtain ⟨x, y, _, rfl⟩ := hL
  exact generateLine_close_right ha hb hc

lemma Set.IsLine.close_left {L : Set V} (hL : L.IsLine) {a b c : V} (ha : a ∈ L) (hb : b ∈ L)
    (hc : sbtw c a b) : c ∈ L := by
  obtain ⟨x, y, _, rfl⟩ := hL
  exact generateLine_close_left ha hb hc

lemma Set.IsLine.close_middle {L : Set V} (hL : L.IsLine) {a b c : V} (ha : a ∈ L) (hb : b ∈ L)
    (hc : sbtw a c b) : c ∈ L := by
  obtain ⟨x, y, _, rfl⟩ := hL
  exact generateLine_close_middle ha hb hc

lemma Set.IsLine.generateLine_subset {S L : Set V} (hL₀ : S ⊆ L) (hL : L.IsLine) :
    GenerateLine S ⊆ L :=
  generateLine_minimal hL₀ hL.close_right hL.close_middle

attribute [local simp] Set.subset_def

variable {x y z : V}

section NotCollinear

def NotCollinear (x y z : V) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ∀ l : Set V, l.IsLine → ¬ {x, y, z} ⊆ l

lemma notCollinear_iff :
    NotCollinear x y z ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ∀ l : Set V, l.IsLine → ¬ {x, y, z} ⊆ l := Iff.rfl

lemma NotCollinear.rotate (h : NotCollinear u v w) : NotCollinear v w u :=
  ⟨h.2.2.1, h.1.symm, h.2.1.symm,
   fun l h₁ h₂ => h.2.2.2 l h₁ (h₂.trans' (by simp))⟩

lemma NotCollinear.swap (h : NotCollinear u v w) : NotCollinear w v u :=
  ⟨h.2.2.1.symm, h.2.1.symm, h.1.symm,
   fun l h₁ h₂ => h.2.2.2 l h₁ (h₂.trans' (by simp))⟩

variable [Nontrivial V]

lemma exists_isLine (a b : V) : ∃ L : Set V, L.IsLine ∧ {a, b} ⊆ L := by
  rcases ne_or_eq a b with h | rfl
  · exact ⟨Line a b, Line_isLine h, by simp⟩
  have ⟨b, h⟩ := exists_ne a
  exact ⟨Line a b, Line_isLine h.symm, by simp⟩

lemma NotCollinear.mk (hl : ∀ l : Set V, l.IsLine → ¬ {x, y, z} ⊆ l) : NotCollinear x y z := by
  refine ⟨?_, ?_, ?_, hl⟩
  · rintro rfl
    obtain ⟨L, hL, hL'⟩ := exists_isLine x z
    aesop
  · rintro rfl
    obtain ⟨L, hL, hL'⟩ := exists_isLine x y
    aesop
  · rintro rfl
    obtain ⟨L, hL, hL'⟩ := exists_isLine x y
    aesop

variable [Finite V]

theorem thm_two (h : ∀ x y z : V, ¬ NotCollinear x y z) :
    (Set.univ : Set V).IsLine := by
  let S : Set (Set V) := setOf Set.IsLine
  have : S.Nonempty := let ⟨x, y, hxy⟩ := exists_pair_ne V; ⟨_, Line_isLine hxy⟩
  obtain ⟨L, hL, hL'⟩ := S.toFinite.exists_maximal_wrt id S this
  dsimp at hL'
  suffices L = Set.univ by rwa [← this]
  rw [Set.eq_univ_iff_forall]
  by_contra!
  obtain ⟨a, b, hab, rfl⟩ := hL
  obtain ⟨c, hc'⟩ := this
  have hac : a ≠ c := fun h => hc' (subset_generateLine _ (by simp [h]))
  have hbc : b ≠ c := fun h => hc' (subset_generateLine _ (by simp [h]))
  simp only [NotCollinear, not_and, not_forall, not_not] at h
  obtain ⟨M, hM, habc⟩ := h a b c hab hac hbc
  have := hL' M hM (Set.IsLine.generateLine_subset (habc.trans' (by simp)) hM)
  rw [this] at hc'
  exact hc' (habc (by simp))

theorem thm_two' (h : ∀ x y z : V, ¬ NotCollinear x y z) :
    ∃ l : Set V, l = Set.univ ∧ l.IsLine :=
  ⟨Set.univ, rfl, thm_two h⟩

end NotCollinear

section IsSimpleTriangle

@[simps]
def simpleEdges : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∀ x, ¬ sbtw a x b
  symm a b := fun | ⟨hab, h⟩ => ⟨hab.symm, fun x hx => h x hx.symm⟩

def IsSimpleTriangle (x y z : V) : Prop :=
  simpleEdges.Adj x y ∧ simpleEdges.Adj y z ∧ simpleEdges.Adj z x ∧ NotCollinear x y z

lemma IsSimpleTriangle.swap (h : IsSimpleTriangle u v w) : IsSimpleTriangle w v u :=
⟨h.2.1.symm, h.1.symm, h.2.2.1.symm, h.2.2.2.swap⟩

variable [Finite V]

lemma one_implies_two (h : ∃ x y z : V, NotCollinear x y z) :
    ∃ x y z : V, IsSimpleTriangle x y z := by
  let S : Set (V × V × V) := setOf (fun ⟨a, b, c⟩ => NotCollinear a b c)
  have : S.Nonempty := let ⟨x, y, z, hxyz⟩ := h; ⟨(x, y, z), hxyz⟩
  let f : V × V × V → ℝ := fun ⟨a, b, c⟩ => dist a b + dist b c + dist c a
  obtain ⟨⟨a, b, c⟩, (h₁ : NotCollinear _ _ _), h₂⟩ := S.toFinite.exists_minimal_wrt f S this
  simp only [Prod.forall, Set.mem_setOf_eq] at h₂
  replace h₂ : ∀ a' b' c' : V, NotCollinear a' b' c' →
      dist a b + dist b c + dist c a ≤ dist a' b' + dist b' c' + dist c' a' := by
    intro a' b' c' hL
    by_contra! h
    exact h.ne' (h₂ a' b' c' hL h.le)
  simp only [IsSimpleTriangle]
  by_contra! cont
  wlog hab : ¬ simpleEdges.Adj a b generalizing a b c
  · rw [not_not] at hab
    refine cont a b c hab ?_ ?_ h₁
    · exact not_not.1 <| this b c a h₁.rotate <|
        fun _ _ _ h => (h₂ _ _ _ h).trans_eq' <| by ring
    · exact not_not.1 <| this c a b h₁.rotate.rotate <|
        fun _ _ _ h => (h₂ _ _ _ h).trans_eq' <| by ring
  simp only [simpleEdges_adj, h₁.1, ne_eq, not_false_eq_true, true_and, not_forall, not_not] at hab
  obtain ⟨d, adb⟩ := hab
  have habc : c ∉ Line a b := fun hc ↦ h₁.2.2.2 (Line a b) (Line_isLine h₁.1)
      (by simp [left_mem_Line, right_mem_Line, hc])
  have hdab : d ∈ Line a b := middle_extend_mem_Line adb
  have hcd : c ≠ d := (habc <| · ▸ hdab)
  have : dist d c < dist d b + dist b c := by
    by_contra!
    refine habc (generateLine_close_right hdab right_mem_Line ?_)
    exact ⟨adb.ne23, hcd.symm, h₁.2.2.1, this.antisymm (dist_triangle _ _ _)⟩
  replace : dist a d + dist d c + dist c a < dist a b + dist b c + dist c a := by
    linarith only [this, adb.2.2.2]
  replace : ¬ NotCollinear a d c := fun h => (h₂ a d c h).not_lt this
  simp only [notCollinear_iff, adb.ne12, hcd.symm, h₁.2.1, true_and, not_and, forall_true_left,
    ne_eq, not_forall, not_not, exists_prop, not_false_eq_true] at this
  obtain ⟨L, hL, hL'⟩ := this
  simp only [Set.subset_def, Set.mem_singleton_iff, Set.mem_insert_iff, forall_eq_or_imp,
    forall_eq] at hL'
  have : b ∈ L := hL.close_right hL'.1 hL'.2.1 adb
  refine h₁.2.2.2 L hL ?_
  simp [this, hL'.1, hL'.2.2]

end IsSimpleTriangle

def Delta (u v w : V) : ℝ := dist u v + dist v w - dist u w

lemma Delta_comm {u v w : V} : Delta u v w = Delta w v u := by
  simp only [Delta, add_comm, dist_comm]

lemma Delta_pos_of {u v w : V} (h : NotCollinear u v w) : 0 < Delta u v w := by
  rw [Delta]
  by_contra!
  have : sbtw u v w := sbtw_mk h.1 h.2.2.1 (by linarith only [this])
  exact h.2.2.2 (Line u v) (Line_isLine this.ne12) (by simp [right_extend_mem_Line this])

lemma exists_third {a b : V} (hab : a ≠ b) (h : Line a b ≠ {a, b}) :
    ∃ c, c ∈ Line a b ∧ (sbtw c a b ∨ sbtw a c b ∨ sbtw a b c) := by
  by_contra! h'
  have : Line a b = {a, b} := by
    refine (subset_generateLine _).antisymm' ?_
    change Line a b ⊆ {a, b}
    refine generateLine_minimal le_rfl ?_ ?_
    · rintro x y z (rfl | rfl) (rfl | rfl) h
      · exact (h.ne12 rfl).elim
      · exact ((h' z (right_extend_mem_Line h)).2.2 h).elim
      · exact ((h' z (left_extend_mem_Line h.symm)).1 h.symm).elim
      · exact (h.ne12 rfl).elim
    · rintro x y z (rfl | rfl) (rfl | rfl) h
      · exact (h.ne13 rfl).elim
      · exact ((h' z (middle_extend_mem_Line h)).2.1 h).elim
      · exact ((h' z (middle_extend_mem_Line h.symm)).2.1 h.symm).elim
      · exact (h.ne13 rfl).elim
  exact h this

lemma eqn_7 {a b c d : V} (habc : IsSimpleTriangle a b c)
    (habc_min : ∀ a' b' c' : V, IsSimpleTriangle a' b' c' → Delta a b c ≤ Delta a' b' c')
    (hacd : sbtw a c d) (hcd : simpleEdges.Adj c d) :
    ¬ simpleEdges.Adj b d := by
  intro h
  have hbcd : NotCollinear b c d := by
    refine ⟨habc.2.1.ne, h.ne, hcd.ne, fun l hl h ↦ ?_⟩
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.subset_def, forall_eq_or_imp,
      forall_eq] at h
    refine habc.2.2.2.2.2.2 l hl (by simp [*, hl.close_left h.2.1 h.2.2 hacd])
  replace hbcd : IsSimpleTriangle b c d := ⟨habc.2.1, hcd, h.symm, hbcd⟩
  have habd : sbtw a b d := by
    refine sbtw_mk habc.1.ne h.ne ?_
    have := habc_min _ _ _ hbcd
    rw [Delta, Delta] at this
    linarith [hacd.dist]
  refine habc.2.2.2.2.2.2 (Line a d) (Line_isLine habd.ne13) ?_
  simp [middle_extend_mem_Line, hacd, habd]

lemma eqn_8 {a b c d : V} (habc : IsSimpleTriangle a b c) (hacd : sbtw a c d) :
    dist a b + dist b d < dist a d + Delta a b c := by
  by_contra!
  have hbcd : sbtw b c d := by
    refine sbtw_mk habc.2.1.ne hacd.ne23 ?_
    rw [Delta] at this
    linarith [hacd.dist]
  refine habc.2.2.2.2.2.2 (Line c d) (Line_isLine hbcd.ne23) ?_
  simp [left_extend_mem_Line, hacd, hbcd]

def List.pathLength : List V → ℝ
| [] | [_] => 0
| (x :: y :: xs) => dist x y + List.pathLength (y :: xs)

lemma List.pathLength_nonneg : (l : List V) → 0 ≤ l.pathLength
  | [] | [_] => by simp [pathLength]
  | (x :: y :: xs) => add_nonneg dist_nonneg (List.pathLength_nonneg _)

lemma List.pathLength_cons_le (x : V) :
    {l : List V} → l.pathLength ≤ (x :: l).pathLength
  | [] => pathLength_nonneg _
  | _ :: _ => le_add_of_nonneg_left dist_nonneg

lemma List.pathLength_triangle_left {v x : V} :
    {l : List V} → (v :: l).pathLength ≤ dist v x + (x :: l).pathLength
  | [] => le_add_of_nonneg_left dist_nonneg
  | _ :: _ => (add_le_add_right (dist_triangle _ _ _) _).trans_eq (add_assoc _ _ _)

lemma List.Sublist.pathLength_sublist {l₁ l₂ : List V} :
    l₁.Sublist l₂ → l₁.pathLength ≤ l₂.pathLength
  | slnil => pathLength_nonneg _
  | cons x h => (pathLength_sublist h).trans (pathLength_cons_le x)
  | cons₂ _ slnil => le_rfl
  | cons₂ x (cons₂ y h) => add_le_add_left (cons₂ y h).pathLength_sublist _
  | cons₂ x (cons y h) => (cons₂ x h).pathLength_sublist.trans pathLength_triangle_left

def List.Special (a b d : V) : List V → Prop
  | [] | [_] | [_, _] => False
  | (a1 :: a2 :: a3 :: l) => a1 = a ∧ NotCollinear a1 a2 a3 ∧
      (¬ simpleEdges.Adj a1 a2 ∨ ¬ simpleEdges.Adj a2 a3) ∧
      List.getLast (a1 :: a2 :: a3 :: l) (by simp) = d ∧
      (a1 :: a2 :: a3 :: l).Chain' (· ≠ ·) ∧
      (a1 :: a2 :: a3 :: l).pathLength ≤ [a, b, d].pathLength

lemma List.Special.pathLength_le {a b d : V} :
    ∀ {P : List V}, P.Special a b d → P.pathLength ≤ [a, b, d].pathLength
  | _ :: _ :: _ :: _, ⟨_, _, _, _, _, h⟩ => h

lemma List.Special.chain_ne {a b d : V} :
    ∀ {P : List V}, P.Special a b d → P.Chain' (· ≠ ·)
  | _ :: _ :: _ :: _, ⟨_, _, _, _, h, _⟩ => h

lemma exists_min_dist (V : Type*) [MetricSpace V] [Finite V] :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : V, x ≠ y → r ≤ dist x y := by
  cases subsingleton_or_nontrivial V
  · exact ⟨1, zero_lt_one, fun x y ↦ by simp [Subsingleton.elim x y]⟩
  let S : Set (V × V) := (Set.diagonal V)ᶜ
  have : S.Nonempty := have ⟨x, y, hxy⟩ := exists_pair_ne V; ⟨(x, y), by simp [S, hxy]⟩
  obtain ⟨⟨x, y⟩, (hxy : x ≠ y), h⟩ := S.toFinite.exists_minimal_wrt (Function.uncurry dist) _ this
  simp only [Set.mem_compl_iff, Set.mem_diagonal_iff, Function.uncurry_apply_pair, Prod.forall] at h
  exact ⟨dist x y, by simp [hxy], fun a b hab => le_of_not_lt (fun h' => h'.ne' (h _ _ hab h'.le))⟩

lemma length_mul_le_pathLength_add {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x y : V, x ≠ y → r ≤ dist x y) :
    {l : List V} → l.Chain' (· ≠ ·) → l.length * r ≤ l.pathLength + r
  | [], _ => by simp [List.pathLength, hr]
  | [_], _ => by simp [List.pathLength]
  | x :: y :: xs, h' => by
      simp only [List.chain'_cons] at h'
      rw [List.pathLength, List.length, Nat.cast_add_one, add_one_mul (α := ℝ), add_assoc,
        add_comm]
      exact add_le_add (h _ _ h'.1) (length_mul_le_pathLength_add hr h h'.2)

lemma uniformly_bounded_of_chain_ne_of_pathLength_le (V : Type*) [MetricSpace V] [Finite V]
    (R : ℝ) :
    ∃ n : ℕ, ∀ l : List V, l.Chain' (· ≠ ·) → l.pathLength ≤ R → l.length ≤ n := by
  have ⟨r, hr, hr'⟩ := exists_min_dist V
  refine ⟨⌊R / r + 1⌋₊, ?_⟩
  intro l hl hl'
  have hR : 0 ≤ R := l.pathLength_nonneg.trans hl'
  have := length_mul_le_pathLength_add hr.le hr' hl
  rw [Nat.le_floor_iff, div_add_one hr.ne', le_div_iff₀ hr]
  · linarith
  · positivity

lemma abd_special {a b c d : V} (habc : IsSimpleTriangle a b c) (hacd : sbtw a c d) (hbd' : b ≠ d)
    (hbd : ¬ simpleEdges.Adj b d) :
    [a, b, d].Special a b d := by
  simp only [List.Special, ne_eq, List.getLast_cons, List.getLast_singleton', and_true, hbd,
    or_true, true_and, List.nodup_cons, List.nodup_nil, List.not_mem_nil, List.mem_cons,
    List.mem_singleton, or_false, hbd', hacd.ne13, notCollinear_iff, habc.1.ne, Set.subset_def,
    Set.mem_singleton_iff, Set.mem_insert_iff, forall_eq_or_imp, forall_eq, le_refl,
    List.chain'_cons, List.chain'_singleton, not_false_eq_true, reduceCtorEq]
  intro l hl hl'
  exact habc.2.2.2.2.2.2 l hl $ by simp [*, hl.close_middle hl'.1 hl'.2.2 hacd]

lemma eqn_9 {a b c d : V} {P : List V} (habc : IsSimpleTriangle a b c) (hacd : sbtw a c d)
    (hbd' : b ≠ d) (hbd : ¬ simpleEdges.Adj b d)
    (hP' : ∀ P' : List V, P'.Special a b d → P.pathLength ≤ P'.pathLength) :
    P.pathLength < dist a d + Delta a b c := by
  refine (hP' [a, b, d] (abd_special habc hacd hbd' hbd)).trans_lt ?_
  rw [List.pathLength, List.pathLength, List.pathLength, add_zero]
  exact eqn_8 habc hacd

variable [Finite V]

lemma exists_simple_split_right {a b : V} (hab : a ≠ b) (hab' : ¬ simpleEdges.Adj a b) :
    ∃ c, sbtw a c b ∧ simpleEdges.Adj c b := by
  simp only [simpleEdges_adj, hab, not_false_eq_true, true_and, ne_eq, not_forall, not_not] at hab'
  obtain ⟨c', hc'⟩ := hab'
  let S : Set V := setOf (sbtw a · b)
  obtain ⟨c, hc : sbtw _ c _, hcmin⟩ := S.toFinite.exists_minimal_wrt (dist b) _ ⟨c', hc'⟩
  refine ⟨c, hc, hc.ne23, fun c' hc' => ?_⟩
  have : dist b c ≤ dist b c' :=
    le_of_not_lt fun h => h.ne' <| hcmin _ (hc.trans_right' hc') h.le
  rw [dist_comm b, dist_comm b] at this
  have : dist c c' ≤ 0 := by linarith [hc'.dist]
  simp only [dist_le_zero] at this
  exact hc'.ne12 this

lemma exists_simple_split_left {a b : V} (hab : a ≠ b) (hab' : ¬ simpleEdges.Adj a b) :
    ∃ c, sbtw a c b ∧ simpleEdges.Adj a c :=
  have ⟨c, hc, hc'⟩ := exists_simple_split_right hab.symm (hab' ·.symm); ⟨c, hc.symm, hc'.symm⟩

variable [Nontrivial V]

lemma case1 {a b c d a₁ a₂ a₃ : V} {l : List V} (habc : IsSimpleTriangle a b c)
    (habc_min : ∀ a' b' c' : V, IsSimpleTriangle a' b' c' → Delta a b c ≤ Delta a' b' c')
    (hacd : sbtw a c d) (hbd' : b ≠ d) (hbd : ¬ simpleEdges.Adj b d)
    (hPmin : ∀ P' : List V, P'.Special a b d → (a₁ :: a₂ :: a₃ :: l).pathLength ≤ P'.pathLength)
    (ha₁ : a₁ = a) (hα : NotCollinear a₁ a₂ a₃)
    (hPd : List.getLast (a₁ :: a₂ :: a₃ :: l) (by simp) = d)
    (hPc : (a₁ :: a₂ :: a₃ :: l).Chain' (· ≠ ·))
    (c₁1 : ¬ simpleEdges.Adj a₁ a₂)
    (c₁2 : ¬ simpleEdges.Adj a₂ a₃) :
    False := by
  have ⟨b₁₂, hb₁₂, hba⟩ := exists_simple_split_right hα.1 c₁1
  have ⟨b₂₃, hb₂₃, hab⟩ := exists_simple_split_left hα.2.2.1 c₁2
  have hb : NotCollinear b₁₂ a₂ b₂₃ := by
    refine NotCollinear.mk fun l hl hl' ↦ ?_
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.subset_def, forall_eq_or_imp,
      forall_eq] at hl'
    have : a₁ ∈ l := hl.close_left hl'.1 hl'.2.1 hb₁₂
    have : a₃ ∈ l := hl.close_right hl'.2.1 hl'.2.2 hb₂₃
    exact hα.2.2.2 l hl (by simp [*, -ha₁])
  classical
  let P' : List V := a₁ :: b₁₂ :: b₂₃ :: a₃ :: l
  have hP' : Delta b₁₂ a₂ b₂₃ = (a₁ :: a₂ :: a₃ :: l).pathLength - P'.pathLength := by
    simp only [List.pathLength, Delta, P']; linarith [hb₁₂.dist, hb₂₃.dist]
  have hd : 0 < Delta b₁₂ a₂ b₂₃ := Delta_pos_of hb
  have hP'lt : P'.pathLength < (a₁ :: a₂ :: a₃ :: l).pathLength := by linarith
  replace hP'ns : ¬ P'.Special a b d := fun hP' ↦ by linarith [hPmin _ hP']
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons] at hPd
  have hP'₁ : NotCollinear a₁ b₁₂ b₂₃ := by
    refine NotCollinear.mk fun l hl hl' ↦ ?_
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.subset_def, forall_eq_or_imp,
      forall_eq] at hl'
    have ha₂ : a₂ ∈ l := hl.close_right hl'.1 hl'.2.1 hb₁₂
    exact hα.2.2.2 l hl (by simp [hl'.1, ha₂, hl.close_right ha₂ hl'.2.2 hb₂₃])
  have ha₃b₂₃ : a₃ ≠ b₂₃ := hb₂₃.ne23.symm
  have ha₃b₁₂ : a₃ ≠ b₁₂ := by
    rintro rfl
    refine hα.2.2.2 (Line a₁ a₃) (Line_isLine hb₁₂.ne12) ?_
    simp [right_extend_mem_Line hb₁₂]
  have hP'₂ : P'.pathLength ≤ (a₁ :: b :: d :: []).pathLength :=
    ha₁ ▸ hP'lt.le.trans (hPmin _ (abd_special habc hacd hbd' hbd))
  have hP'₃ : P'.Chain' (· ≠ ·) := by
    simp only [P', ne_eq, List.chain'_cons] at hPc
    simp only [P', List.chain'_cons, and_true, ← ha₁, hb₁₂.ne12, true_and, not_false_eq_true, ne_eq,
      ha₃b₁₂.symm, ha₃b₂₃.symm, hPc.2.2, hP'₁.2]
  simp only [List.Special, hP'₁, List.getLast_cons_cons, List.getLast_cons_cons, hPd,
    hP'₂, hP'₃, ← ha₁, and_true, true_and, not_or, not_not, P'] at hP'ns
  have : IsSimpleTriangle b₁₂ a₂ b₂₃ := ⟨hba, hab, hP'ns.2.symm, hb⟩
  replace := habc_min _ _ _ this
  have h9 := eqn_9 habc hacd hbd' hbd hPmin
  suffices dist a d ≤ P'.pathLength by linarith
  have : List.Sublist [a, d] P' := by
    rw [← ha₁, List.cons_sublist_cons, List.singleton_sublist]
    have : d ∈ a₃ :: l := by rw [← hPd]; exact List.getLast_mem _
    rw [List.mem_cons, List.mem_cons]
    simp only [this, or_true]
  have := List.Sublist.pathLength_sublist this
  rwa [List.pathLength, List.pathLength, add_zero] at this

lemma case2 {a b c d a₁ a₂ a₃ : V} {l : List V} (habc : IsSimpleTriangle a b c)
    (habc_min : ∀ a' b' c' : V, IsSimpleTriangle a' b' c' → Delta a b c ≤ Delta a' b' c')
    (hacd : sbtw a c d) (hbd' : b ≠ d) (hbd : ¬ simpleEdges.Adj b d)
    (hPmin : ∀ P' : List V, P'.Special a b d → (a₁ :: a₂ :: a₃ :: l).pathLength ≤ P'.pathLength)
    (ha₁ : a₁ = a) (hα : NotCollinear a₁ a₂ a₃)
    (hPd : List.getLast (a₁ :: a₂ :: a₃ :: l) (by simp) = d)
    (hPc : (a₁ :: a₂ :: a₃ :: l).Chain' (· ≠ ·))
    (c₁1 : simpleEdges.Adj a₁ a₂)
    (c₁2 : ¬simpleEdges.Adj a₂ a₃) :
    False := by
  have ⟨b₂₃, hb₂₃, hab⟩ := exists_simple_split_left hα.2.2.1 c₁2
  have hb : NotCollinear a₁ a₂ b₂₃ := by
    refine NotCollinear.mk fun l hl hl' => ?_
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.subset_def, forall_eq_or_imp,
      forall_eq] at hl'
    exact hα.2.2.2 l hl (by simp [hl'.1, hl'.2.1, hl.close_right hl'.2.1 hl'.2.2 hb₂₃])
  have hP'₁ : NotCollinear a₁ b₂₃ a₃ := by
    refine NotCollinear.mk fun l hl hl' ↦ ?_
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.subset_def, forall_eq_or_imp,
      forall_eq] at hl'
    have : a₂ ∈ l := hl.close_left hl'.2.1 hl'.2.2 hb₂₃
    exact hα.2.2.2 l hl (by simp [*, -ha₁])
  classical
  let P' : List V := a₁ :: b₂₃ :: a₃ :: l
  have hP' : Delta a₁ a₂ b₂₃ = (a₁ :: a₂ :: a₃ :: l).pathLength - P'.pathLength := by
    simp only [List.pathLength, Delta, P']; linarith [hb₂₃.dist]
  have hd : 0 < Delta a₁ a₂ b₂₃ := Delta_pos_of hb
  have hP'lt : P'.pathLength < (a₁ :: a₂ :: a₃ :: l).pathLength := by linarith
  replace hP'ns : ¬ P'.Special a b d := fun hP' ↦ by linarith [hPmin _ hP']
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons] at hPd
  have ha₃b₂₃ : a₃ ≠ b₂₃ := hb₂₃.ne23.symm
  have hP'₂ : P'.pathLength ≤ (a₁ :: b :: d :: []).pathLength :=
    ha₁ ▸ hP'lt.le.trans (hPmin _ (abd_special habc hacd hbd' hbd))
  have hP'₃ : P'.Chain' (· ≠ ·) := by
    simp only [P', ne_eq, List.chain'_cons] at hPc
    simp only [P', List.chain'_cons, and_true, ← ha₁, true_and, not_false_eq_true, ne_eq,
      ha₃b₂₃.symm, hPc.2.2, hP'₁.2, hP'₁.1]
  simp only [List.Special, hP'₁, List.getLast_cons_cons, List.getLast_cons_cons, hPd,
    hP'₂, hP'₃, ← ha₁, and_true, true_and, not_or, not_not, P'] at hP'ns
  have : IsSimpleTriangle a₁ a₂ b₂₃ := ⟨c₁1, hab, hP'ns.1.symm, hb⟩
  replace := habc_min _ _ _ this
  have h9 := eqn_9 habc hacd hbd' hbd hPmin
  suffices dist a d ≤ P'.pathLength by linarith
  have : List.Sublist [a, d] P' := by
    rw [← ha₁, List.cons_sublist_cons, List.singleton_sublist]
    have : d ∈ a₃ :: l := by rw [← hPd]; exact List.getLast_mem _
    rw [List.mem_cons]
    simp only [this, or_true]
  have := List.Sublist.pathLength_sublist this
  rwa [List.pathLength, List.pathLength, add_zero] at this

lemma case3 {a b c d a₁ a₂ a₃ : V} {l : List V} (habc : IsSimpleTriangle a b c)
    (habc_min : ∀ a' b' c' : V, IsSimpleTriangle a' b' c' → Delta a b c ≤ Delta a' b' c')
    (hacd : sbtw a c d) (hbd' : b ≠ d) (hbd : ¬ simpleEdges.Adj b d)
    (hPmin : ∀ P' : List V, P'.Special a b d → (a₁ :: a₂ :: a₃ :: l).pathLength ≤ P'.pathLength)
    (ha₁ : a₁ = a) (hα : NotCollinear a₁ a₂ a₃)
    (hPd : List.getLast (a₁ :: a₂ :: a₃ :: l) (by simp) = d)
    (hPc : (a₁ :: a₂ :: a₃ :: l).Chain' (· ≠ ·))
    (c₁1 : ¬simpleEdges.Adj a₁ a₂)
    (c₁2 : simpleEdges.Adj a₂ a₃) :
    False := by
  have ⟨b₁₂, hb₁₂, hba⟩ := exists_simple_split_right hα.1 c₁1
  have hb : NotCollinear b₁₂ a₂ a₃ := by
    refine NotCollinear.mk fun l hl hl' => ?_
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.subset_def, forall_eq_or_imp,
      forall_eq] at hl'
    have : a₁ ∈ l := hl.close_left hl'.1 hl'.2.1 hb₁₂
    exact hα.2.2.2 l hl (by simp [*, -ha₁])
  classical
  let P' : List V := a₁ :: b₁₂ :: a₃ :: l
  have hP' : Delta b₁₂ a₂ a₃ = (a₁ :: a₂ :: a₃ :: l).pathLength - P'.pathLength := by
    simp only [List.pathLength, Delta, P']; linarith [hb₁₂.dist]
  have hd : 0 < Delta b₁₂ a₂ a₃ := Delta_pos_of hb
  have hP'lt : P'.pathLength < (a₁ :: a₂ :: a₃ :: l).pathLength := by linarith
  replace hP'ns : ¬ P'.Special a b d := fun hP' ↦ by linarith [hPmin _ hP']
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons] at hPd
  have hP'₁ : NotCollinear a₁ b₁₂ a₃ := by
    refine NotCollinear.mk fun l hl hl' ↦ ?_
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.subset_def, forall_eq_or_imp,
      forall_eq] at hl'
    exact hα.2.2.2 l hl (by simp [hl'.1, hl.close_right hl'.1 hl'.2.1 hb₁₂, hl'.2.2])
  have ha₃b₁₂ : a₃ ≠ b₁₂ := by
    rintro rfl
    refine hα.2.2.2 (Line a₁ a₃) (Line_isLine hb₁₂.ne12) ?_
    simp [right_extend_mem_Line hb₁₂]
  have hP'₂ : P'.pathLength ≤ (a₁ :: b :: d :: []).pathLength :=
    ha₁ ▸ hP'lt.le.trans (hPmin _ (abd_special habc hacd hbd' hbd))
  have hP'₃ : P'.Chain' (· ≠ ·) := by
    simp only [P', ne_eq, List.chain'_cons] at hPc
    simp only [P', List.chain'_cons, and_true, ← ha₁, hb₁₂.ne12, true_and, not_false_eq_true, ne_eq,
      ha₃b₁₂.symm, hPc.2.2, hP'₁.2]
  simp only [List.Special, hP'₁, List.getLast_cons_cons, List.getLast_cons_cons, hPd,
    hP'₂, hP'₃, ← ha₁, and_true, true_and, not_or, not_not, P'] at hP'ns
  have : IsSimpleTriangle b₁₂ a₂ a₃ := ⟨hba, c₁2, hP'ns.2.symm, hb⟩
  replace := habc_min _ _ _ this
  have h9 := eqn_9 habc hacd hbd' hbd hPmin
  suffices dist a d ≤ P'.pathLength by linarith
  have : List.Sublist [a, d] P' := by
    rw [← ha₁, List.cons_sublist_cons, List.singleton_sublist]
    have : d ∈ a₃ :: l := by rw [← hPd]; exact List.getLast_mem _
    rw [List.mem_cons]
    simp only [this, or_true]
  have := List.Sublist.pathLength_sublist this
  rwa [List.pathLength, List.pathLength, add_zero] at this

lemma two_implies_three (h : ∃ x y z : V, IsSimpleTriangle x y z) :
    ∃ a b : V, a ≠ b ∧ Line a b = {a, b} := by
  let S : Set (V × V × V) := setOf (fun ⟨x, y, z⟩ => IsSimpleTriangle x y z)
  have : S.Nonempty := let ⟨x, y, z, hxyz⟩ := h; ⟨(x, y, z), hxyz⟩
  obtain ⟨⟨a, b, c⟩, (habc : IsSimpleTriangle a b c), hmin⟩ :=
    S.toFinite.exists_minimal_wrt (fun ⟨x, y, z⟩ => Delta x y z) S this
  replace hmin : ∀ a' b' c' : V, IsSimpleTriangle a' b' c' → Delta a b c ≤ Delta a' b' c' := by
    intro a' b' c' h
    by_contra! h'
    exact h'.ne' (hmin (a', b', c') h h'.le)
  refine ⟨a, c, habc.2.2.1.1.symm, ?_⟩
  by_contra! h3
  obtain ⟨d, hd, hd'⟩ := exists_third habc.2.2.1.1.symm h3
  simp only [habc.2.2.1.symm.2 d, false_or] at hd'
  wlog acd : sbtw a c d generalizing a c
  · rw [Line_comm] at hd h3
    rw [Set.pair_comm] at h3
    have h' := hd'.resolve_right acd
    refine this c a habc.swap ?_ h3 hd (Or.inr h'.symm) h'.symm
    intro a' b' c' h'
    rw [Delta_comm]
    exact hmin _ _ _ h'
  clear hd'
  let S : Set V := setOf (sbtw a c)
  obtain ⟨d, hd : sbtw _ _ d, hdmin⟩ := S.toFinite.exists_minimal_wrt (dist c) S ⟨d, acd⟩
  have hbd' : b ≠ d := by
    rintro rfl
    have := habc.2.2.2.2.2.2 (Line a c) (Line_isLine hd.ne12)
    simp [right_extend_mem_Line hd] at this
  replace hdmin : ∀ d', sbtw a c d' → dist c d ≤ dist c d' := by
    intro d' hd'
    by_contra! hd''
    exact hd''.ne' (hdmin d' hd' hd''.le)
  have hcd : simpleEdges.Adj c d := by
    use hd.2.2.1
    intro e he
    have : 0 ≤ dist e d := dist_nonneg
    have : dist e d = 0 := by linarith [he.dist, this, hdmin e (hd.right_cancel he)]
    simp only [dist_eq_zero] at this
    exact he.ne23 this
  have hbd := eqn_7 habc hmin hd hcd
  let S : Set (List V) := setOf (List.Special a b d)
  have : S.Finite := by
    have ⟨n, hn⟩ := uniformly_bounded_of_chain_ne_of_pathLength_le V [a, b, d].pathLength
    exact (List.finite_length_le _ _).subset fun l hl => hn l hl.chain_ne hl.pathLength_le
  have ⟨P, (hP : P.Special a b d), hPmin⟩ :=
    this.exists_minimal_wrt List.pathLength S ⟨[a, b, d], abd_special habc hd hbd' hbd⟩
  replace hPmin : ∀ P' : List V, P'.Special a b d → P.pathLength ≤ P'.pathLength := by
    intro P' hP'
    by_contra! h
    exact h.ne' (hPmin P' hP' h.le)
  match P with
  | (a₁ :: a₂ :: a₃ :: l) =>
    simp only [List.Special] at hP
    rcases hP with ⟨ha₁, hα, hβ, hPd, hPc, _⟩
    have : (¬ simpleEdges.Adj a₁ a₂ ∧ ¬ simpleEdges.Adj a₂ a₃) ∨
          (simpleEdges.Adj a₁ a₂ ∧ ¬ simpleEdges.Adj a₂ a₃) ∨
          (¬ simpleEdges.Adj a₁ a₂ ∧ simpleEdges.Adj a₂ a₃) := by tauto
    rcases this with (⟨c₁1, c₁2⟩ | ⟨c₂1, c₂2⟩ | ⟨c₃1, c₃2⟩)
    · exact case1 habc hmin hd hbd' hbd hPmin ha₁ hα hPd hPc c₁1 c₁2
    · exact case2 habc hmin hd hbd' hbd hPmin ha₁ hα hPd hPc c₂1 c₂2
    · exact case3 habc hmin hd hbd' hbd hPmin ha₁ hα hPd hPc c₃1 c₃2

theorem sylvester_chvatal (V : Type*) [MetricSpace V] [Nontrivial V] [Finite V] :
    ∃ a b : V, a ≠ b ∧ (Line a b = {a, b} ∨ Line a b = Set.univ) := by
  by_cases h : ∀ x y z : V, ¬ NotCollinear x y z
  · obtain ⟨L, hL, a, b, hab, rfl⟩ := thm_two' h
    exact ⟨a, b, hab, Or.inr hL⟩
  push_neg at h
  replace h := one_implies_two h
  obtain ⟨a, b, h, hl⟩ := two_implies_three h
  exact ⟨a, b, h, Or.inl hl⟩

end

-- variable {n : ℕ} {a b c : Fin n → ℝ}

-- -- Sbtw.left_mem_affineSpan

-- lemma sbtw_iff_Sbtw : sbtw a b c ↔ Sbtw ℝ a b c := by
--   rw [MetricSpace.sbtw_iff, Sbtw, Wbtw]
--   suffices : dist a b + dist b c = dist a c ↔ b ∈ affineSegment ℝ a c


-- theorem Line_eq_line {n : ℕ} {a b : Fin n → ℝ} : Line a b = line[Fin n → ℝ, a, b] := by

--   sorry

-- theorem sylvester_gallai {S : Finset (Fin 2 → ℝ)} :
--   ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
