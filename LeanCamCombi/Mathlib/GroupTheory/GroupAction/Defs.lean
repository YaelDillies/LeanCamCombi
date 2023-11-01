import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.SMulWithZero

@[simp]
lemma smul_boole {M A} [Zero A] [SMulZeroClass M A] (P : Prop) [Decidable P] (a : M) (b : A) :
    (a • if P then b else 0) = if P then a • b else 0 := by rw [smul_ite, smul_zero]

@[simp]
lemma boole_smul {M A} [MonoidWithZero M] [AddCommMonoid A] [MulActionWithZero M A] (P : Prop)
    [Decidable P] (a : A) : (if P then (1 : M) else 0) • a = if P then a else 0 := by
  rw [ite_smul, one_smul, zero_smul]
