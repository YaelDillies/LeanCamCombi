import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Submodule
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {s t : Submodule R M}

-- TODO: Generalise `finrank_mono`

lemma rank_mono (hst : s ≤ t) : Module.rank R s ≤ Module.rank R t := rank_le_of_submodule _ _ hst

end Submodule
