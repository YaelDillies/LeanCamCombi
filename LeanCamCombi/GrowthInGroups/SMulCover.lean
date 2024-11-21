import Mathlib.Data.Real.Basic
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Finset Pointwise

variable {M N X : Type*} [Monoid M] [Monoid N] [MulAction M X] [MulAction N X] {K L : ℝ}
  {A A₁ A₂ B B₁ B₂ C : Set X}

variable (M) in
@[to_additive] def SMulCovered (K : ℝ) (A B : Set X) : Prop :=
  ∃ F : Finset M, #F ≤ K ∧ A ⊆ (F : Set M) • B

@[to_additive (attr := simp, refl)]
lemma SMulCovered.rfl : SMulCovered M 1 A A := ⟨1, by simp⟩

@[to_additive (attr := simp)]
lemma SMulCovered.of_subset (hAB : A ⊆ B) : SMulCovered M 1 A B := ⟨1, by simpa⟩

@[to_additive] lemma SMulCovered.nonneg : SMulCovered M K A B → 0 ≤ K := by
  rintro ⟨F, hF, -⟩; exact (#F).cast_nonneg.trans hF

@[to_additive (attr := simp)]
lemma smulCovered_zero : SMulCovered M 0 A B ↔ A = ∅ := by simp [SMulCovered]

@[to_additive]
lemma SMulCovered.mono (hKL : K ≤ L) : SMulCovered M K A B → SMulCovered M L A B := by
  rintro ⟨F, hF, hFAB⟩; exact ⟨F, hF.trans hKL, hFAB⟩

@[to_additive] lemma SMulCovered.trans [MulAction M N] [IsScalarTower M N X]
    (hAB : SMulCovered M K A B) (hBC : SMulCovered N L B C) : SMulCovered N (K * L) A C := by
  classical
  have := hAB.nonneg
  obtain ⟨F₁, hF₁, hFAB⟩ := hAB
  obtain ⟨F₂, hF₂, hFBC⟩ := hBC
  refine ⟨F₁ • F₂, ?_, ?_⟩
  · calc
      (#(F₁ • F₂) : ℝ) ≤ #F₁ * #F₂ := mod_cast Finset.card_smul_le
      _ ≤ K * L := by gcongr
  · calc
      A ⊆ (F₁ : Set M) • B := hFAB
      _ ⊆ (F₁ : Set M) • (F₂ : Set N) • C := by gcongr
      _ = (↑(F₁ • F₂) : Set N) • C := by simp

@[to_additive]
lemma SMulCovered.subset_left (hA : A₁ ⊆ A₂) (hAB : SMulCovered M K A₂ B) :
    SMulCovered M K A₁ B := by simpa using (SMulCovered.of_subset (M := M) hA).trans hAB

@[to_additive]
lemma SMulCovered.subset_right (hB : B₁ ⊆ B₂) (hAB : SMulCovered M K A B₁) :
    SMulCovered M K A B₂ := by simpa using hAB.trans (.of_subset (M := M) hB)

@[to_additive]
lemma SMulCovered.subset (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) (hAB : SMulCovered M K A₂ B₁) :
    SMulCovered M K A₁ B₂ := (hAB.subset_left hA).subset_right hB
