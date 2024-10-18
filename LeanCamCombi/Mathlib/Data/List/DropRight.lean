import Batteries.Data.List.Perm
import Mathlib.Data.List.DropRight
import Mathlib.Data.Nat.Defs

namespace List
variable {α : Type*} {l l' l₀ l₁ l₂ : List α} {a b : α} {m n : ℕ}

lemma rtake_suffix (n : ℕ) (l : List α) : l.rtake n <:+ l := drop_suffix _ _

lemma length_rtake (n : ℕ) (l : List α) : (l.rtake n).length = min n l.length :=
  (length_drop _ _).trans $ by rw [Nat.sub_sub_eq_min, min_comm]

@[simp] lemma take_reverse' (n : ℕ) (l : List α) : l.reverse.take n = (l.rtake n).reverse := by
  rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp] lemma rtake_reverse (n : ℕ) (l : List α) : l.reverse.rtake n = (l.take n).reverse := by
  rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp] lemma rtake_rtake (n m) (l : List α) : (l.rtake m).rtake n = l.rtake (min n m) := by
  rw [rtake_eq_reverse_take_reverse, ← take_reverse', take_take, rtake_eq_reverse_take_reverse]

@[simp] lemma rdrop_append_rtake (n : ℕ) (l : List α) : l.rdrop n ++ l.rtake n = l :=
  take_append_drop _ _

lemma suffix_iff_eq_rtake : l₁ <:+ l₂ ↔ l₁ = l₂.rtake (length l₁) :=
  ⟨fun h ↦ append_cancel_left $ (suffix_iff_eq_append.1 h).trans (rdrop_append_rtake _ _).symm,
    fun e ↦ e.symm ▸ rtake_suffix _ _⟩

alias ⟨IsPrefix.eq_take, _⟩ := prefix_iff_eq_take
alias ⟨IsSuffix.eq_rtake, _⟩ := suffix_iff_eq_rtake

@[simp] lemma take_min : l.take (min n l.length) = l.take n := sorry
@[simp] lemma drop_min : l.drop (min n l.length) = l.drop n := sorry
@[simp] lemma rtake_min : l.rtake (min n l.length) = l.rtake n := sorry
@[simp] lemma rdrop_min : l.rdrop (min n l.length) = l.rdrop n := sorry

lemma take_prefix_take (h : m ≤ n) : l.take m <+: l.take n := by
  rw [prefix_iff_eq_take, length_take, take_take, Nat.min_right_comm, min_eq_left h, take_min]

lemma drop_suffix_drop (h : m ≤ n) : l.drop n <:+ l.drop m := sorry

lemma rtake_suffix_rtake (h : m ≤ n) : l.rtake m <:+ l.rtake n :=
  drop_suffix_drop $ Nat.sub_le_sub_left h _

lemma rdrop_prefix_rdrop (h : m ≤ n) : l.rdrop n <+: l.rdrop m :=
  take_prefix_take $ Nat.sub_le_sub_left h _

protected lemma IsPrefix.take (hl : l <+: l') (h : l.length ≤ n) : l <+: l'.take n := by
  rw [hl.eq_take]; exact take_prefix_take h

protected lemma IsSuffix.rtake (hl : l <:+ l') (h : l.length ≤ n) : l <:+ l'.rtake n := by
  rw [hl.eq_rtake]; exact rtake_suffix_rtake h

lemma exists_prefix_length_eq (hn : n ≤ l.length) : ∃ l', l' <+: l ∧ l'.length = n :=
  ⟨l.take n, take_prefix _ _, (length_take _ _).trans $ min_eq_left hn⟩

lemma exists_suffix_length_eq (hn : n ≤ l.length) : ∃ l', l' <:+ l ∧ l'.length = n :=
  ⟨l.rtake n, rtake_suffix _ _, (length_rtake _ _).trans $ min_eq_left hn⟩

lemma exists_sublist_length_eq (hn : n ≤ l.length) : ∃ l', l' <+ l ∧ l'.length = n :=
  ⟨l.take n, take_sublist _ _, (length_take _ _).trans $ min_eq_left hn⟩

lemma IsPrefix.exists_intermediate (hl : l₀ <+: l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
    ∃ l₁, l₀ <+: l₁ ∧ l₁ <+: l₂ ∧ l₁.length = n :=
  ⟨l₂.take n, hl.take h₀, take_prefix _ _, (length_take _ _).trans $ min_eq_left h₂⟩

lemma IsSuffix.exists_intermediate (hl : l₀ <:+ l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
    ∃ l₁, l₀ <:+ l₁ ∧ l₁ <:+ l₂ ∧ l₁.length = n :=
  ⟨l₂.rtake n, hl.rtake h₀, rtake_suffix _ _, (length_rtake _ _).trans $ min_eq_left h₂⟩

lemma Sublist.exists_intermediate (hl : l₀ <+ l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
    ∃ l₁, l₀ <+ l₁ ∧ l₁ <+ l₂ ∧ l₁.length = n := by
  induction' l₀ with a l₀ ih generalizing n l₂
  · exact (exists_sublist_length_eq h₂).imp (fun l₁ h ↦ ⟨nil_sublist _, h⟩)
  cases n
  · cases h₀
  cases' l₂ with b l₂
  · cases h₂
  obtain ⟨l₁, h₀₁, h₁₂, rfl⟩ := ih sorry (Nat.succ_le_succ_iff.1 h₀) (Nat.le_of_succ_le h₂)
  rw [cons_sublist_cons'] at hl
  obtain hl | ⟨rfl, hl⟩ := hl
  stop
  · obtain ⟨l₁, h₀₁, h₁₂, rfl⟩ := ih _ (Nat.succ_le_succ_iff.1 h₀) (Nat.succ_le_succ_iff.1 h₂)
    refine ⟨l₁, hl, _⟩

lemma Subperm.exists_intermediate (hl : l₀ <+~ l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
    ∃ l₁, l₀ <+~ l₁ ∧ l₁ <+~ l₂ ∧ l₁.length = n := by
  obtain ⟨l₀', hl₀, hl'⟩ := hl
  obtain ⟨l₁, h₀₁, h₁₂, hn⟩ := hl'.exists_intermediate (hl₀.length_eq.trans_le h₀) h₂
  exact ⟨l₁, ⟨_, hl₀, h₀₁⟩, h₁₂.subperm, hn⟩

lemma exists_subperm_length_eq (hn : n ≤ l.length) : ∃ l', l' <+~ l ∧ l'.length = n := by
  simpa using nil_subperm.exists_intermediate (Nat.zero_le _) hn

end List
