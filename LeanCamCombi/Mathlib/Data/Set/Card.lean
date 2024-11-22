import Mathlib.Data.Set.Card

namespace Set
variable {R α : Type*} {s t : Set α}

local prefix:arg "#" => Set.ncard

-- TODO: Replace `ncard_diff`
lemma ncard_sdiff (hst : s ⊆ t) (hs : s.Finite) : #(t \ s) = #t - #s := by
  obtain ht | ht := t.finite_or_infinite
  · rw [← ncard_diff_add_ncard_of_subset hst ht, add_tsub_cancel_right]
  · rw [ht.ncard, Nat.zero_sub, (ht.diff hs).ncard]

lemma cast_ncard_sdiff [AddGroupWithOne R] (hst : s ⊆ t) (ht : t.Finite) :
    (#(t \ s) : R) = #t - #s := by
  rw [ncard_sdiff hst (ht.subset hst), Nat.cast_sub (ncard_le_ncard hst ht)]

attribute [gcongr] ncard_le_ncard

end Set
