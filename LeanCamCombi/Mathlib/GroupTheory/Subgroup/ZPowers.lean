import Mathlib.GroupTheory.Subgroup.ZPowers

section Group
variable {α : Type*} [Group α] {s : Subgroup α} {a : α} {m n : ℤ}

open Function Int Set Subgroup Submonoid

@[to_additive] lemma range_zpow (a : α) : (range fun n : ℤ => a ^ n) = zpowers a := rfl

end Group
