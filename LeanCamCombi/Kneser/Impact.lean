/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.Additive.Etransform
import LeanCamCombi.Mathlib.Data.Finset.Pointwise
import LeanCamCombi.Mathlib.Data.Set.Finite
import LeanCamCombi.Mathlib.Data.Nat.Lattice
import LeanCamCombi.Kneser.Mathlib

/-!
# Impact function
-/

open Function
open scoped Pointwise

namespace Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

section Mul
variable [Mul α] {n : ℕ}

/-- The multiplicative impact function of a finset. -/
@[to_additive]
noncomputable def mulImpact (s : Finset α) (n : ℕ) : ℕ :=
  ⨅ t : { t : Finset α // t.card = n }, (s * t).card

@[to_additive (attr := simp)]
lemma mulImpact_empty (n : ℕ) : (∅ : Finset α).mulImpact n = 0 := by simp [mulImpact]

end Mul

section Group
variable [Group α] {n : ℕ}

@[to_additive (attr := simp)]
lemma mulImpact_singleton [Infinite α] (a : α) (n : ℕ) : ({a} : Finset α).mulImpact n = n := by
  simp only [mulImpact, singleton_mul', card_smul_finset]
  haveI : Nonempty { t : Finset α // t.card = n } := nonempty_subtype.2 (exists_card _)
  exact Eq.trans (iInf_congr Subtype.prop) ciInf_const

variable [Fintype α]

@[to_additive]
lemma exists_mulImpact_add_mulImpact (s : Finset α) (hn : 2 ≤ n) (hnα : n < Fintype.card α)
    (hnα' : ¬n ∣ Fintype.card α) :
    ∃ k, 0 < k ∧ k < n ∧ s.mulImpact (n - k) + s.mulImpact (n + k) ≤ 2 * s.mulImpact n :=
  sorry

end Group

section CommGroup
variable [CommGroup α] [CommGroup β] {n : ℕ}

@[to_additive]
lemma mulImpact_map_of_infinite [Infinite α] (s : Finset α) (f : α →* β) (hf : Injective f) :
    mulImpact (s.map ⟨f, hf⟩) n = mulImpact s n := by
  haveI : Infinite β := sorry
  haveI : Nonempty { t : Finset α // t.card = n } := nonempty_subtype.2 (exists_card _)
  haveI : Nonempty { t : Finset β // t.card = n } := nonempty_subtype.2 (exists_card _)
  refine' le_antisymm _ _
  · refine' le_ciInf fun t => _
    sorry
  · refine' le_ciInf fun t => _
    sorry

@[to_additive]
lemma mulImpact_map_of_fintype [Fintype α] (s : Finset α) (f : α →* β) (hf : Injective f) :
    mulImpact (s.map ⟨f, hf⟩) n = mulImpact s (Fintype.card α * (n / Fintype.card α)) :=
  sorry

end CommGroup
end Finset
