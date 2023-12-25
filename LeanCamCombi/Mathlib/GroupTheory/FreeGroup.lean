import Mathlib.GroupTheory.FreeGroup

namespace FreeGroup

variable {α : Type _} [DecidableEq α]

attribute [simp] to_word_inv

@[to_additive]
theorem toWord_mul_sublist (x y : FreeGroup α) : (x * y).toWord <+ x.toWord ++ y.toWord := by
  refine' red.sublist _
  have : x * y = FreeGroup.mk (x.to_word ++ y.to_word) := by
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
  rw [this]
  exact FreeGroup.reduce.red

end FreeGroup
