import Mathlib.GroupTheory.Submonoid.Operations

namespace Submonoid

variable {G α β : Type*} [Monoid G] [SMul G α] {S : Submonoid G}

@[to_additive (attr := simp)]
lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a :=
  rfl

end Submonoid
