import Mathlib.Data.Set.Finite
import Tactic.IntervalCases

open Function

-- This may already exist in some form in Mathlib.
theorem Equiv.symm_apply_mem_of_forall_mem_finite {α : Type _} (e : α ≃ α) {s : Set α}
    (h_mem : ∀ x : s, e x ∈ s) (h_fin : s.Finite) (x : s) : e.symm (x : α) ∈ s := by
  haveI : Fintype s := Set.Finite.fintype h_fin
  let f : s → s := fun x => ⟨e x, h_mem x⟩
  have h_inj : injective f := by rintro ⟨a, ha⟩ ⟨b, hb⟩ hab; simpa using hab
  have h_surj : surjective f := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨h_inj, rfl⟩).2
  obtain ⟨y, rfl⟩ := h_surj x
  change e.symm (e y) ∈ s
  simp

theorem Nat.eq_one_or_two_or_four_of_div_four {n : ℕ} (h : n ∣ 4) : n = 1 ∨ n = 2 ∨ n = 4 := by
  have h₁ := Nat.le_of_dvd four_pos h
  interval_cases h : n <;> revert h <;> decide
