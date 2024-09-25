import Mathlib.Combinatorics.SetFamily.Shatter

open scoped BigOperators FinsetFamily

namespace Finset
variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α} {n : ℕ}

attribute [gcongr] shatterer_mono

@[gcongr] lemma vcDim_mono (h𝒜ℬ : 𝒜 ⊆ ℬ) : 𝒜.vcDim ≤ ℬ.vcDim := by unfold vcDim; gcongr

end Finset
