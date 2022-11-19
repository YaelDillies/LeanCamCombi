import data.fintype.basic

@[simp] lemma fintype.univ_Prop : (finset.univ : finset Prop) = {true, false} :=
finset.eq_of_veq $ by simp; refl
