/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `Finset.StronglyShatters`:
* `Finset.OrderShatters`:

## TODO

* Order-shattering
* Strong shattering
-/

open scoped FinsetFamily

namespace Finset
variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α} {n : ℕ}

/-! ### Strong shattering -/

def StronglyShatters (𝒜 : Finset (Finset α)) (s : Finset α) : Prop :=
  ∃ t, ∀ ⦃u⦄, u ⊆ s → ∃ v ∈ 𝒜, s ∩ v = u ∧ v \ s = t

/-! ### Order shattering -/

section order
variable [LinearOrder α]

def OrderShatters : Finset (Finset α) → List α → Prop
  | 𝒜, [] => 𝒜.Nonempty
  | 𝒜, a :: l => (𝒜.nonMemberSubfamily a).OrderShatters l ∧ (𝒜.memberSubfamily a).OrderShatters l
      ∧ ∀ ⦃s : Finset α⦄, s ∈ 𝒜.nonMemberSubfamily a → ∀ ⦃t⦄, t ∈ 𝒜.memberSubfamily a →
        {x ∈ s | a < x} = {x ∈ t | a < x}

instance instDecidableRel : DecidableRel (OrderShatters (α := α)) := fun 𝒜 l ↦ by
  induction l generalizing 𝒜
  · exact decidableNonempty
  · exact instDecidableAnd

def orderShatterser (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s ∈ 𝒜.biUnion powerset | 𝒜.OrderShatters $ s.sort (· ≤ ·)}

end order

end Finset
