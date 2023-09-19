import Mathlib.Data.Fintype.Basic

namespace Finset
variable {α : Type*} {p : α → Prop} [DecidablePred p] {s t : Finset α} [Fintype {a // p a}]

@[simp] lemma subtype_eq_univ : s.subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [ext_iff]
@[simp] lemma subtype_univ [Fintype α] : univ.subtype p = univ := by simp

variable [Fintype α] [DecidableEq α]

@[simp] lemma inter_eq_univ : s ∩ t = univ ↔ s = univ ∧ t = univ := inf_eq_top_iff
@[simp] lemma compl_subset_compl_iff : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (Finset α) _ _ _

end Finset

namespace Fintype
variable {α : Type*} [Fintype α]

@[simp, norm_cast] lemma coe_finsetEquivSet : ⇑finsetEquivSet = ((↑) : Finset α → Set α) := rfl

/-- Given a fintype `α`, `finsetOrderIsoSet` is the order isomorphism between `Finset α` and `Set α`
(all sets on a finite type are finite). -/
@[simps toEquiv]
noncomputable def finsetOrderIsoSet : Finset α ≃o Set α where
  toEquiv := finsetEquivSet
  map_rel_iff' := Finset.coe_subset

@[simp, norm_cast]
lemma coe_finsetOrderIsoSet : ⇑finsetOrderIsoSet = ((↑) : Finset α → Set α) := rfl

@[simp] lemma coe_finsetOrderIsoSet_symm :
    ⇑(finsetOrderIsoSet : Finset α ≃o Set α).symm = ⇑finsetEquivSet.symm := rfl

end Fintype
