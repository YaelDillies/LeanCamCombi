import Order.Zorn
import Mathlib.Order.Chain

#align_import mathlib.order.zorn

variable {α : Type _}

/-! ### Flags -/


namespace Flag

variable [Preorder α] {c : Set α} {s : Flag α} {a b : α}

theorem IsChain.exists_subset_flag (hc : IsChain (· ≤ ·) c) : ∃ s : Flag α, c ⊆ s :=
  let ⟨s, hs, hcs⟩ := hc.exists_maxChain
  ⟨hs.Flag, hcs⟩

theorem exists_mem (a : α) : ∃ s : Flag α, a ∈ s :=
  let ⟨s, hs⟩ := Set.subsingleton_singleton.IsChain.exists_subset_flag
  ⟨s, hs rfl⟩

theorem exists_mem_mem (hab : a ≤ b) : ∃ s : Flag α, a ∈ s ∧ b ∈ s := by
  simpa [Set.insert_subset_iff] using (isChain_pair _ hab).exists_subset_flag

instance : Nonempty (Flag α) :=
  ⟨maxChain_spec.Flag⟩

end Flag

