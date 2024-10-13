/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic
import LeanCamCombi.Kneser.Kneser

/-!
# The Cauchy-Davenport theorem as a corollary of Kneser's lemma

This file proves the Cauchy-Davenport theorem as a corollary of Kneser's lemma.

## Main declarations

* `ZMod.min_le_card_add'`: The Cauchy-Davenport theorem.

## Tags

additive combinatorics, number theory, sumset, cauchy-davenport
-/

open Finset
open scoped Pointwise

/-- The **Cauchy-Davenport Theorem**. -/
lemma ZMod.cauchy_davenport' {p : ℕ} (hp : p.Prime) {s t : Finset (ZMod p)} (hs : s.Nonempty)
    (ht : t.Nonempty) : min p (s.card + t.card - 1) ≤ (s + t).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain h | h := eq_bot_or_eq_top (AddAction.stabilizer (ZMod p) (s + t))
  · refine min_le_of_right_le ?_
    rw [← AddSubgroup.coe_set_eq_zero, ← coe_addStab (hs.add ht), coe_eq_zero] at h
    simpa [*] using add_kneser s t
  · rw [← AddSubgroup.coe_eq_univ, ← coe_addStab (hs.add ht), coe_eq_univ] at h
    refine card_addStab_le_card.trans' ?_
    simp [*, card_univ]
