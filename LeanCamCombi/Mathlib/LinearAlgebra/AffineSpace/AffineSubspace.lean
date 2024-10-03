import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

/-!
# TODO

Kill `spanPoints`
-/

open Set
open scoped Pointwise

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

@[simp]
lemma vectorSpan_add_self (s : Set V) : (vectorSpan k s : Set V) + s = affineSpan k s := by
  ext
  simp [mem_add, spanPoints]
  aesop

@[simp] lemma affineSpan_insert_zero (s : Set V) :
    (affineSpan k (insert 0 s) : Set V) = Submodule.span k s := by
  rw [← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self, vectorSpan_def]
  refine Subset.trans ?_ <| subset_add_left _ <| mem_insert ..
  gcongr
  exact subset_sub_left <| mem_insert ..
