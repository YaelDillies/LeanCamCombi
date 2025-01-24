import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Opposite
import Mathlib.Order.RelIso.Group

namespace RelIso
variable {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r ≃r r` on `α`. -/
instance applyMulAction : MulAction (r ≃r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action by `r ≃r r` on `α`. -/
instance applyOpMulAction : MulAction (r ≃r r)ᵐᵒᵖ α where
  smul e := e.unop.symm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma smul_def (f : r ≃r r) (a : α) : f • a = f a := rfl
@[simp] lemma op_smul_def (f : (r ≃r r)ᵐᵒᵖ) (a : α) : f • a = f.unop.symm a := rfl

instance apply_faithfulSMul : FaithfulSMul (r ≃r r) α where eq_of_smul_eq_smul h := RelIso.ext h

instance apply_op_faithfulSMul : FaithfulSMul (r ≃r r)ᵐᵒᵖ α :=
  sorry

end RelIso
