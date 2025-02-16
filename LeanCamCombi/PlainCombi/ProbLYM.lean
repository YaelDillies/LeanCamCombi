/-
Copyright (c) 2024 Ching-Tsun Chou, Chris Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Chris Wong
-/
import LeanCamCombi.Mathlib.Algebra.BigOperators.Field
import LeanCamCombi.PlainCombi.KatonaCircle

/-!
# The LYM inequality using probability theory

This file proves the LYM inequality using (very elementary) probability theory.



## References

This proof formalizes Section 1.2 of Prof. Yufei Zhao's lecture notes for MIT 18.226:

<https://yufeizhao.com/pm/probmethod_notes.pdf>

A video of Prof. Zhao's lecture is available on YouTube:

<https://youtu.be/exBXHYl4po8>

The proof of Theorem 1.10, Lecture 3 in the Cambridge lecture notes on combinatorics:

<https://github.com/YaelDillies/maths-notes/blob/master/combinatorics.pdf>

is basically the same proof, except without using probability theory.
-/

open Finset Fintype Numbering

variable {α : Type*} [Fintype α] {𝒜 : Finset (Finset α)}

/-- The **Lubell-Yamamoto-Meshalkin inequality**, proved using the Katona circle method. -/
theorem LYM_inequality (h𝒜 : IsAntichain (· ⊆ ·) 𝒜.toSet) :
    ∑ s ∈ 𝒜, ((card α).choose #s : ℚ≥0)⁻¹ ≤ 1 := by
  classical
  calc
    _ = ∑ s ∈ 𝒜, (prefixed s).dens := by simp
    _ = (𝒜.biUnion prefixed).dens := by
      rw [dens_biUnion]
      exact fun s hs t ht hst ↦ disjoint_prefixed_prefixed (h𝒜 hs ht hst) (h𝒜 ht hs hst.symm)
    _ ≤ 1 := dens_le_one
