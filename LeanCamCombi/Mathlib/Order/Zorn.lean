import Mathlib.Order.Zorn
import LeanCamCombi.Mathlib.Order.Chain

variable {α : Type}

/-! ### Flags -/

namespace Flag

variable [Preorder α] {c : Set α} {s : Flag α} {a b : α}

theorem _root_.IsChain.exists_subset_flag (hc : IsChain (· ≤ ·) c) : ∃ s : Flag α, c ⊆ s :=
  let ⟨s, hs, hcs⟩ := hc.exists_maxChain; ⟨ofIsMaxChain s hs, hcs⟩

theorem exists_mem (a : α) : ∃ s : Flag α, a ∈ s :=
  let ⟨s, hs⟩ := Set.subsingleton_singleton (a := a).isChain.exists_subset_flag
  ⟨s, hs rfl⟩

theorem exists_mem_mem (hab : a ≤ b) : ∃ s : Flag α, a ∈ s ∧ b ∈ s := by
  simpa [Set.insert_subset_iff] using (isChain_pair _ hab).exists_subset_flag

instance : Nonempty (Flag α) := ⟨.ofIsMaxChain _ maxChain_spec⟩

end Flag
