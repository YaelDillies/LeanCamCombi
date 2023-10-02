import Mathlib.Order.Category.BoolAlg
import Mathlib.Order.Hom.CompleteLattice

open CategoryTheory OrderDual Opposite Set

universe u

/-- The powerset functor. `set` as a functor. -/
def typeToBoolAlgOp : Type u ⥤ BoolAlgᵒᵖ where
  obj X := op $ BoolAlg.of (Set X)
  map {X Y} f := Quiver.Hom.op
    (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
