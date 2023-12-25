/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Combinatorics.Additive.Behrend
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Tactic.LinearCombination
import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to a most one triangle.
The lower bound comes from turning the big Salem-Spencer set from Behrend's lower bound on Roth
numbers into a graph that has the property that every triangle gives a (possibly trivial)
arithmetic progression on the original set.

## Main declarations

* `simple_graph.ruzsa_szemeredi_number`
* `ruzsa_szemeredi_number_nat_lower_bound`: Explicit lower bound on htThe Ruzsa-Szemerédi graph associated to a set `s`.
* `add_salem_spencer.edge_disjoint_triangles`: If `s` is Salem-Spencer, then `add_graph s` has
  edge-disjoint triangles.
-/


namespace Nat

variable {a b : ℕ}

theorem le_mul_div_add (hb : b ≠ 0) : a ≤ b * (a / b) + b - 1 :=
  le_tsub_of_add_le_right <| by
    rw [succ_le_iff, ← mul_add_one, mul_comm, ← div_lt_iff_lt_mul (pos_iff_ne_zero.2 hb),
      lt_add_one_iff]

end Nat

open Finset

open Fintype (card)

open Nat Real SimpleGraph Sum3 SimpleGraph.TripartiteFromTriangles

open scoped Pointwise

variable {α β : Type _}

/-! ### The Ruzsa-Szemerédi number -/


namespace SimpleGraph

variable (α) [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {G H : SimpleGraph α}

/-- The Ruzsa-Szemerédi number of a fintype is the cardinality of its greatest locally linear simple
graph. -/
noncomputable def ruzsaSzemerediNumber : ℕ := by
  classical exact
    Nat.findGreatest (fun m => ∃ G : SimpleGraph α, (G.cliqueFinset 3).card = m ∧ G.LocallyLinear)
      ((card α).choose 3)

theorem ruzsaSzemerediNumber_le : ruzsaSzemerediNumber α ≤ (card α).choose 3 :=
  Nat.findGreatest_le _

theorem ruzsaSzemerediNumber_spec :
    ∃ G : SimpleGraph α, (G.cliqueFinset 3).card = ruzsaSzemerediNumber α ∧ G.LocallyLinear :=
  @Nat.findGreatest_spec _ _
    (fun m => ∃ G : SimpleGraph α, (G.cliqueFinset 3).card = m ∧ G.LocallyLinear) _ (Nat.zero_le _)
    ⟨⊥, by simp, locallyLinear_bot⟩

variable {α} {n : ℕ}

theorem LocallyLinear.le_ruzsaSzemerediNumber [DecidableRel G.Adj] (hG : G.LocallyLinear) :
    (G.cliqueFinset 3).card ≤ ruzsaSzemerediNumber α :=
  le_findGreatest card_cliqueFinset_le ⟨G, by congr, hG⟩

theorem ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsaSzemerediNumber α ≤ ruzsaSzemerediNumber β := by
  refine' find_greatest_mono _ (choose_mono _ <| Fintype.card_le_of_embedding f)
  rintro n ⟨G, rfl, hG⟩
  refine' ⟨G.map f, _, hG.map _⟩
  rw [← card_map ⟨map f, Finset.map_injective _⟩, ← clique_finset_map G f]
  congr
  decide

theorem ruzsaSzemerediNumber_congr (e : α ≃ β) : ruzsaSzemerediNumber α = ruzsaSzemerediNumber β :=
  (ruzsaSzemerediNumber_mono (e : α ↪ β)).antisymm <| ruzsaSzemerediNumber_mono e.symm

noncomputable def ruzsaSzemerediNumberNat (n : ℕ) : ℕ :=
  ruzsaSzemerediNumber (Fin n)

@[simp]
theorem ruzsaSzemerediNumberNat_card : ruzsaSzemerediNumberNat (card α) = ruzsaSzemerediNumber α :=
  ruzsaSzemerediNumber_congr (Fintype.equivFin _).symm

theorem ruzsaSzemerediNumberNat_mono : Monotone ruzsaSzemerediNumberNat := fun m n h =>
  ruzsaSzemerediNumber_mono (Fin.castLEEmb h).toEmbedding

theorem ruzsaSzemerediNumberNat_le : ruzsaSzemerediNumberNat n ≤ n.choose 3 :=
  (ruzsaSzemerediNumber_le _).trans_eq <| by rw [Fintype.card_fin]

@[simp]
theorem ruzsa_szmeredi_number_nat_zero : ruzsaSzemerediNumberNat 0 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

@[simp]
theorem ruzsa_szmeredi_number_nat_one : ruzsaSzemerediNumberNat 1 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

@[simp]
theorem ruzsa_szmeredi_number_nat_two : ruzsaSzemerediNumberNat 2 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

end SimpleGraph

open SimpleGraph

/-! ### The Ruzsa-Szemerédi construction -/


namespace RuzsaSzemeredi

variable [Fintype α] [CommRing α] {s : Finset α} {x : α × α × α}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The triangle indices for the Ruzsa-Szemerédi construction. -/
private def triangle_indices (s : Finset α) : Finset (α × α × α) :=
  (univ ×ˢ s).map
    ⟨fun xa => (xa.1, xa.1 + xa.2, xa.1 + 2 * xa.2), by
      rintro ⟨x, a⟩ ⟨y, b⟩ h
      simp only [Prod.ext_iff] at h
      obtain rfl := h.1
      obtain rfl := add_right_injective _ h.2.1
      rfl⟩

@[simp]
theorem mem_triangleIndices : x ∈ triangleIndices s ↔ ∃ y, ∃ a ∈ s, (y, y + a, y + 2 * a) = x := by
  simp [triangle_indices]

@[simp]
theorem card_triangleIndices : (triangleIndices s).card = card α * s.card := by
  simp [triangle_indices, card_univ]

theorem noAccidental (hs : AddSalemSpencer (s : Set α)) :
    NoAccidental (triangleIndices s : Finset (α × α × α)) :=
  ⟨by
    simp only [mem_triangle_indices, Prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp]
    rintro _ _ _ _ _ _ d a ha rfl rfl rfl b' b hb rfl rfl h₁ d' c hc rfl h₂ rfl
    have : a + c = b + b := by linear_combination h₁.symm - h₂.symm
    obtain rfl := hs ha hc hb this
    simp_all⟩

variable [Fact <| IsUnit (2 : α)]

instance : ExplicitDisjoint (triangleIndices s : Finset (α × α × α))
    where
  inj₀ := by
    simp only [mem_triangle_indices, Prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h₁ h₂
    linear_combination 2 * h₁.symm - h₂.symm
  inj₁ := by
    simp only [mem_triangle_indices, Prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl rfl h
    simpa [(Fact.out <| IsUnit (2 : α)).mul_right_inj, eq_comm] using h
  inj₂ := by
    simp only [mem_triangle_indices, Prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h rfl
    simpa [(Fact.out <| IsUnit (2 : α)).mul_right_inj, eq_comm] using h

theorem locallyLinear (hs : AddSalemSpencer (s : Set α)) :
    (graph <| (triangleIndices s : Finset (α × α × α))).LocallyLinear :=
  haveI := no_accidental hs
  tripartite_from_triangles.locally_linear _

theorem card_edgeFinset (hs : AddSalemSpencer (s : Set α)) [DecidableEq α] :
    (graph <| (triangleIndices s : Finset (α × α × α))).edgeFinset.card = 3 * card α * s.card := by
  haveI := no_accidental hs
  rw [(locally_linear hs).card_edgeFinset, card_triangles, card_triangle_indices, mul_assoc]

end RuzsaSzemeredi

open RuzsaSzemeredi

variable (α) [Fintype α] [DecidableEq α] [CommRing α] [Fact <| IsUnit (2 : α)]

theorem addRothNumber_le_ruzsaSzemerediNumber :
    card α * addRothNumber (univ : Finset α) ≤ ruzsaSzemerediNumber (Sum α (Sum α α)) := by
  obtain ⟨s, -, hscard, hs⟩ := addRothNumber_spec (univ : Finset α)
  haveI := no_accidental hs
  rw [← hscard, ← card_triangle_indices, ← card_triangles]
  exact (locally_linear hs).le_ruzsaSzemerediNumber

theorem rothNumberNat_le_ruzsaSzemerediNumberNat (n : ℕ) :
    (2 * n + 1) * rothNumberNat n ≤ ruzsaSzemerediNumberNat (6 * n + 3) := by
  refine'
    (mul_le_mul_left'
          ((Fin.rothNumberNat_le_addRothNumber le_rfl).trans <|
            add_roth_number.mono <| subset_univ _)
          _).trans
      _
  rw [← Fintype.card_fin (2 * n + 1)]
  have : Nat.Coprime 2 (2 * n + 1) := by simp
  haveI : Fact (IsUnit (2 : Fin (2 * n + 1))) := ⟨by simpa using (ZMod.unitOfCoprime 2 this).IsUnit⟩
  refine' (addRothNumber_le_ruzsaSzemerediNumber _).trans_eq _
  simp_rw [← ruzsa_szemeredi_number_nat_card, Fintype.card_sum, Fintype.card_fin]
  ring_nf

theorem rothNumberNat_le_ruzsa_szemeredi_number_nat' :
    ∀ n : ℕ, (n / 3 - 2 : ℝ) * rothNumberNat ((n - 3) / 6) ≤ ruzsaSzemerediNumberNat n
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    calc
      _ ≤ (↑(2 * (n / 6) + 1) : ℝ) * rothNumberNat (n / 6) :=
        mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      _ ≤ (ruzsa_szemeredi_number_nat (6 * (n / 6) + 3) : ℝ) := _
      _ ≤ _ :=
        Nat.cast_le.2 (ruzsa_szemeredi_number_nat_mono <| add_le_add_right (Nat.mul_div_le _ _) _)
    · norm_num
      rw [← div_add_one (three_ne_zero' ℝ), ← le_sub_iff_add_le, div_le_iff (zero_lt_three' ℝ),
        add_assoc, add_sub_assoc, add_mul, mul_right_comm]
      norm_num
      norm_cast
      exact (Nat.le_mul_div_add <| show 6 ≠ 0 by norm_num).trans (by norm_num)
    · norm_cast
      exact rothNumberNat_le_ruzsaSzemerediNumberNat _

theorem ruzsaSzemerediNumberNat_lower_bound (n : ℕ) :
    (n / 3 - 2 : ℝ) * ↑((n - 3) / 6) * exp (-4 * sqrt (log ↑((n - 3) / 6))) ≤
      ruzsaSzemerediNumberNat n := by
  rw [mul_assoc]
  obtain hn | hn := le_total (n / 3 - 2 : ℝ) 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hn <| by positivity).trans (Nat.cast_nonneg _)
  exact
    (mul_le_mul_of_nonneg_left Behrend.roth_lower_bound hn).trans
      (rothNumberNat_le_ruzsa_szemeredi_number_nat' _)

open Asymptotics Filter

theorem ruzsaSzemerediNumberNat_asymptotic :
    IsBigO atTop (fun n => n ^ 2 * exp (-4 * sqrt (log n)) : ℕ → ℝ) fun n =>
      (ruzsaSzemerediNumberNat n : ℝ) := by
  have :
    is_O at_top
      (fun n => (n / 3 - 2) * ↑((n - 3) / 6) * NormedSpace.exp (-4 * sqrt (log ↑((n - 3) / 6))) :
        ℕ → ℝ)
      fun n => (ruzsa_szemeredi_number_nat n : ℝ) := by
    refine' is_O.of_bound 1 _
    simp only [neg_mul, norm_eq_abs, norm_coe_nat, one_mul, eventually_at_top, ge_iff_le]
    refine' ⟨6, fun n hn => _⟩
    simpa using abs_le_abs_of_nonneg _ (ruzsaSzemerediNumberNat_lower_bound n)
    have : (0 : ℝ) ≤ n / 3 - 2 := sorry
    positivity
  simp_rw [sq]
  refine' is_O.trans _ this
  refine' (is_O.mul _ _).mul _
  sorry
  sorry
  sorry
