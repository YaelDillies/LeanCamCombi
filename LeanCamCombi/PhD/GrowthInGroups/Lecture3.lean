import Mathlib.Algebra.Group.Commutator
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic

variable {G : Type*} [NormedGroup G] {a b : G}

lemma norm_commutator_sub_one_le : ‖⁅a, b⁆ - 1‖ ≤
