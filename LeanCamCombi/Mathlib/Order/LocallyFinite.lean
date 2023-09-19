import Mathlib.Order.LocallyFinite

namespace Set
variable {α : Type*} [Preorder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[simp] lemma toFinset_Icc (a b : α) [Fintype (Icc a b)] : (Icc a b).toFinset = Finset.Icc a b := by
  ext; simp

@[simp] lemma toFinset_Ico (a b : α) [Fintype (Ico a b)] : (Ico a b).toFinset = Finset.Ico a b := by
  ext; simp

@[simp] lemma toFinset_Ioc (a b : α) [Fintype (Ioc a b)] : (Ioc a b).toFinset = Finset.Ioc a b := by
  ext; simp

@[simp] lemma toFinset_Ioo (a b : α) [Fintype (Ioo a b)] : (Ioo a b).toFinset = Finset.Ioo a b := by
  ext; simp

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[simp]
lemma toFinset_Ici (a : α) [Fintype (Ici a)] : (Ici a).toFinset = Finset.Ici a := by ext; simp

@[simp]
lemma toFinset_Ioi (a : α) [Fintype (Ioi a)] : (Ioi a).toFinset = Finset.Ioi a := by ext; simp

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[simp]
lemma toFinset_Iic (a : α) [Fintype (Iic a)] : (Iic a).toFinset = Finset.Iic a := by ext; simp

@[simp]
lemma toFinset_Iio (a : α) [Fintype (Iio a)] : (Iio a).toFinset = Finset.Iio a := by ext; simp

end LocallyFiniteOrderBot
end Set

namespace Finset
variable {α : Type*}

section SemilatticeSup
variable [SemilatticeSup α] [OrderBot α] [LocallyFiniteOrderBot α]

@[simp] lemma sup_Iic (a : α) : (Iic a).sup id = a :=
  le_antisymm (Finset.sup_le λ _ ↦ mem_Iic.1) $ le_sup (f := id) $ mem_Iic.2 $ le_refl a

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [OrderTop α] [LocallyFiniteOrderTop α]

@[simp] lemma inf_Ici (a : α) : (Ici a).inf id = a :=
  le_antisymm (inf_le (f := id) $ mem_Ici.2 $ le_refl a) $ Finset.le_inf λ _ ↦ mem_Ici.1

end SemilatticeInf
end Finset
