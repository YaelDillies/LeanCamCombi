
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic

example (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∀ i, ![1, -ε 1, -ε 0] i = 1 ∨ ![1, -ε 1, -ε 0] i = -1 := by
  intros i
  fin_cases i
  · simp
  · simpa [or_comm, neg_eq_iff_eq_neg] using hε 1
  · simpa [or_comm, neg_eq_iff_eq_neg] using hε 0
