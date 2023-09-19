import Mathlib.Data.SetLike.Basic

namespace SetLike
variable {A B : Type*} [SetLike A B] {p q : A}

@[norm_cast] lemma coe_ne_coe : (p : Set B) ≠ q ↔ p ≠ q := coe_injective.ne_iff

end SetLike
