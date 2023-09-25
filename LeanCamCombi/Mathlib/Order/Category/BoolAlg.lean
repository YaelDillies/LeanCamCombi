import Mathlib.Order.Category.BoolAlgCat
import Mathlib.Order.Hom.CompleteLattice

open CategoryTheory OrderDual Opposite Set

universe u

/-- The powerset functor. `set` as a functor. -/
def typeToBoolAlgOp : Type u ⥤ BoolAlgCatᵒᵖ where
  obj X := op $ BoolAlgCat.of (Set X)
  map {X Y} f := Quiver.Hom.op
    (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
