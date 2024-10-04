import Mathlib.Order.Interval.Finset.Defs

open OrderDual

variable {α : Type*} [Preorder α]

namespace Finset
section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

lemma Icc_orderDual_def (a b : αᵒᵈ) :
    Icc a b = (Icc (ofDual b) (ofDual a)).map toDual.toEmbedding := map_refl.symm

lemma Ico_orderDual_def (a b : αᵒᵈ) :
    Ico (toDual a) (toDual b) = (Ioc b a).map toDual.toEmbedding := map_refl.symm

lemma Ioc_orderDual_def (a b : αᵒᵈ) :
    Ioc (toDual a) (toDual b) = (Ico b a).map toDual.toEmbedding := map_refl.symm

lemma Ioo_orderDual_def (a b : αᵒᵈ) :
    Ioo (toDual a) (toDual b) = (Ioo b a).map toDual.toEmbedding := map_refl.symm

end LocallyFiniteOrder
end Finset
