import Mathlib.Order.Closure

-- TODO: Protect: `ClosureOperator.id`

open Set

variable {α : Type*}

namespace ClosureOperator
section PartialOrder
variable [PartialOrder α] {c : ClosureOperator α} {x y : α}

lemma le_closure_iff_forall : x ≤ c y ↔ ∀ z, y ≤ z → z ∈ c.closed → x ≤ z := by
  refine ⟨λ hxy z hyz hz ↦ ?_, λ h ↦ h _ (le_closure _ _) $ closure_is_closed _ _⟩
  rw [←closure_eq_self_of_mem_closed _ hz, le_closure_iff] at hyz ⊢
  rw [le_closure_iff] at hxy
  exact hxy.trans hyz

end PartialOrder

variable [CompleteLattice α] {p : α → Prop}

/-- Define a closure operator from a predicate that's preserved under infima. -/
def ofPred (p : α → Prop) (hsinf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : ClosureOperator α :=
  ClosureOperator.mk₃ (λ a ↦ ⨅ b : {b // p b ∧ a ≤ b}, b) p
    (λ a ↦ by simp [forall_swap])
    (λ a ↦ hsinf _ $ forall_range_iff.2 $ λ b ↦ b.2.1)
    (λ a b hab hb ↦ iInf_le_of_le ⟨b, hb, hab⟩ le_rfl)

/-- This lemma shows that the image of `x` of a closure operator built from the `ofPred` constructor
respects `p`, the property that was fed into it. -/
lemma ofPred_spec {sinf} (x : α) : p (ofPred p sinf x) := closure_mem_mk₃ _

/-- The property `p` fed into the `ofPred` constructor exactly corresponds to being closed. -/
@[simp] lemma closed_ofPred {hsinf} : (ofPred p hsinf).closed = {x | p x} := by
  ext; exact mem_mk₃_closed

/-- The property `p` fed into the `ofPred` constructor exactly corresponds to being closed. -/
lemma mem_closed_ofPred {hsinf} {x : α} : x ∈ (ofPred p hsinf).closed ↔ p x := mem_mk₃_closed

end ClosureOperator
