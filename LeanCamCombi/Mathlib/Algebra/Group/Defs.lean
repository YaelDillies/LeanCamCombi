import Mathlib.Algebra.Group.Defs

/-- An `AddCancelSemigroup` is an additive semigroup such that `a + b = a + c` implies `b = c`,
and `a + c = b + c` implies `a = b`. -/
class AddCancelSemigroup (α : Type*) extends AddLeftCancelSemigroup α, AddRightCancelSemigroup α

/-- A `CancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`, and
`a * c = b * c` implies `a = b`. -/
@[to_additive]
class CancelSemigroup (α : Type*) extends LeftCancelSemigroup α, RightCancelSemigroup α

attribute [to_additive existing] CancelSemigroup.toRightCancelSemigroup
