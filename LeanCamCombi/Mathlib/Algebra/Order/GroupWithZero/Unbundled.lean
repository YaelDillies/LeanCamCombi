import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

instance {α} [Mul α] [Preorder α] [MulLeftMono α] [Zero α] : PosMulMono α where
  elim _ _ _ hyz := mul_le_mul_left' hyz _

instance {α} [Mul α] [Preorder α] [MulRightMono α] [Zero α] : MulPosMono α where
  elim _ _ _ hyz := mul_le_mul_right' hyz _
