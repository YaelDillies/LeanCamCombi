import Mathlib.GroupTheory.FreeGroup.Basic

open scoped List

namespace FreeGroup
variable {α : Type*} [DecidableEq α]

attribute [simp] toWord_inv

@[to_additive]
theorem toWord_mul_sublist (x y : FreeGroup α) : (x * y).toWord <+ x.toWord ++ y.toWord := by
  refine Red.sublist ?_
  have : x * y = FreeGroup.mk (x.toWord ++ y.toWord) := by
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
  rw [this]
  exact FreeGroup.reduce.red

@[to_additive (attr := simp)]
lemma reduce_nil : reduce ([] : List (α × Bool)) = [] :=
  rfl

@[to_additive]
lemma reduce_singleton (s : α × Bool) : reduce [s] = [s] :=
  rfl

end FreeGroup
