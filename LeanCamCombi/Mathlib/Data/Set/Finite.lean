import Mathlib.Data.Set.Finite

open Set

namespace List
variable (α : Type*) [Finite α] (n : ℕ)

lemma finite_length_eq : {l : List α | l.length = n}.Finite := by
  induction n with
  | zero => simp [List.length_eq_zero]
  | succ n ih =>
    suffices {l : List α | l.length = n + 1} = Set.univ.image2 (· :: ·) {l | l.length = n} by
      rw [this]; exact Set.finite_univ.image2 _ ih
    ext (_ | _) <;> simp [n.succ_ne_zero.symm]

lemma finite_length_lt : {l : List α | l.length < n}.Finite := by
  convert (Finset.range n).finite_toSet.biUnion fun i _ ↦ finite_length_eq α i; ext; simp

lemma finite_length_le : {l : List α | l.length ≤ n}.Finite := by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)
