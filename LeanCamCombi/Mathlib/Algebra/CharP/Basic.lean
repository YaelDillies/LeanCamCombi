import Mathlib.Algebra.CharP.Basic

variable (R : Type _)

theorem CharP.nat_cast_injOn_Iio [AddGroupWithOne R] (p : ℕ) [CharP R p] :
    (Set.Iio p).InjOn (coe : ℕ → R) := fun a ha b hb hab =>
  ((CharP.natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb
