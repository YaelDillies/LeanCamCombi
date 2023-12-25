import Mathlib.Algebra.Group.Opposite
import GroupTheory.GroupAction.Defs
import Order.RelIso.Group

namespace RelIso

variable {α : Type _} {r : α → α → Prop}

/-- The tautological action by `r ≃r r` on `α`. -/
instance applyMulAction : MulAction (r ≃r r) α
    where
  smul := coeFn
  one_smul _ := rfl
  hMul_smul _ _ _ := rfl

/-- The tautological action by `r ≃r r` on `α`. -/
instance applyOpMulAction : MulAction (r ≃r r)ᵐᵒᵖ α
    where
  smul e := e.unop.symm
  one_smul _ := rfl
  hMul_smul _ _ _ := rfl

@[simp]
theorem smul_def (f : r ≃r r) (a : α) : f • a = f a :=
  rfl

@[simp]
theorem op_smul_def (f : (r ≃r r)ᵐᵒᵖ) (a : α) : f • a = f.unop.symm a :=
  rfl

instance apply_faithfulSMul : FaithfulSMul (r ≃r r) α :=
  ⟨RelIso.ext⟩

instance apply_op_faithfulSMul : FaithfulSMul (r ≃r r)ᵐᵒᵖ α :=
  sorry

end RelIso
