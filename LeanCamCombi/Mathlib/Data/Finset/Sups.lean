import Mathlib.Data.Finset.Slice
import Mathlib.Data.Finset.Sups

/-!
# Set family operations

This file defines a few binary operations on `Finset α` for use in set family combinatorics.

## Main declarations

* `Finset.diffs`: Finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`.
* `Finset.compls`: Finset of elements of the form `aᶜ` where `a ∈ s`.

## Notation

We define the following notation in locale `FinsetFamily`:
* `s \\ t` for `Finset.diffs`
* `sᶜˢ` for `Finset.compls`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

-- TODO: Is there a better spot for those two instances? Why are they not already inferred from
-- `instDecidablePredMemUpperClosure`, `instDecidablePredMemLowerClosure`?
namespace Finset
variable {α : Type*} [Preorder α] [@DecidableRel α (· ≤ ·)] {s : Finset α}

instance decidablePredMemUpperClosure : DecidablePred (· ∈ upperClosure (s : Set α)) :=
  fun _ ↦ decidableExistsAndFinset
#align finset.decidable_pred_mem_upper_closure Finset.decidablePredMemUpperClosure

instance decidablePredMemLowerClosure : DecidablePred (· ∈ lowerClosure (s : Set α)) :=
  fun _ ↦ decidableExistsAndFinset
#align finset.decidable_pred_mem_lower_closure Finset.decidablePredMemLowerClosure

end Finset

open Fintype Function
open scoped FinsetFamily

variable {F α β : Type*} [DecidableEq α] [DecidableEq β]

namespace Finset
section SemilatticeSup
variable [Fintype α] [SemilatticeSup α] [SemilatticeSup β] [SupHomClass F α β] {s : Finset α}

@[simp] lemma univ_sups_univ : (univ : Finset α) ⊻ univ = univ := top_le_iff.1 subset_sups_self

end SemilatticeSup

section SemilatticeInf
variable [Fintype α] [SemilatticeInf α] [SemilatticeInf β] [InfHomClass F α β] {s : Finset α}

@[simp] lemma univ_infs_univ : (univ : Finset α) ⊼ univ = univ := top_le_iff.1 subset_infs_self

end SemilatticeInf

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α}

@[simp] lemma powerset_sups_powerset_self (s : Finset α) :
    s.powerset ⊻ s.powerset = s.powerset := by simp [←powerset_union]

@[simp] lemma powerset_infs_powerset_self (s : Finset α) :
    s.powerset ⊼ s.powerset = s.powerset := by simp [←powerset_inter]

lemma union_mem_sups : s ∈ 𝒜 → t ∈ ℬ → s ∪ t ∈ 𝒜 ⊻ ℬ := sup_mem_sups
lemma inter_mem_infs : s ∈ 𝒜 → t ∈ ℬ → s ∩ t ∈ 𝒜 ⊼ ℬ := inf_mem_infs

end Finset
