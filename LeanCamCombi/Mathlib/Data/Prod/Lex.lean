import Mathlib.Data.Prod.Lex

namespace Prod.Lex
variable {α β : Type*} [PartialOrder α] [Preorder β] [WellFoundedLT α] [WellFoundedLT β]

instance : WellFoundedLT (α ×ₗ β) := instIsWellFoundedProdLex

end Prod.Lex
