import Mathlib.Algebra.Ring.Hom.Defs

namespace RingHom
variable {R : Type*} [Semiring R]

@[simp, norm_cast] lemma coe_id : ⇑(id R) = _root_.id := rfl

end RingHom
