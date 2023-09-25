import Mathlib.Order.BooleanAlgebra

namespace Prod
variable {α β : Type*} [GeneralizedBooleanAlgebra α] [GeneralizedBooleanAlgebra β]

instance instGeneralizedBooleanAlgebra : GeneralizedBooleanAlgebra (α × β) where
  sup_inf_sdiff _ _ := ext (sup_inf_sdiff _ _) (sup_inf_sdiff _ _)
  inf_inf_sdiff _ _ := ext (inf_inf_sdiff _ _) (inf_inf_sdiff _ _)

end Prod
