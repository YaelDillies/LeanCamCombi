import data.fintype.basic

@[simp] lemma fintype.univ_Prop : (finset.univ : finset Prop) = {true, false} :=
finset.eq_of_veq $ by simp; refl

attribute [simp] finset.inter_eq_left_iff_subset finset.inter_eq_right_iff_subset
  finset.sdiff_eq_empty_iff_subset

namespace finset
variables {α : Type*} [fintype α] {s t : finset α}

lemma codisjoint_left : codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t :=
by { classical, simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left] }

lemma codisjoint_right : codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s :=
by rw [codisjoint.comm, codisjoint_left]

-- TODO: Turn `disjoint_val` around

variables [decidable_eq α]

instance decidable_codisjoint : decidable (codisjoint s t) :=
decidable_of_iff _ codisjoint_left.symm

instance decidable_is_compl : decidable (is_compl s t) := decidable_of_iff' _ is_compl_iff

end finset
