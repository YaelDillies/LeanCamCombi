import Mathlib.Order.SuccPred.Archimedean

namespace Order
variable {α β : Type*} [Preorder α] [Preorder β] [SuccOrder α] [IsSuccArchimedean α]
  {s : Set α} {f : α → β}

lemma monotoneOn_of_le_succ (hs : s.OrdConnected)
    (hf : ∀ a, a ∈ s → succ a ∈ s → f a ≤ f (succ a)) : MonotoneOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab
  clear hab
  induction' n with n hn
  · simp
  rw [Function.iterate_succ_apply'] at hb ⊢
  have : succ^[n] a ∈ s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
  exact (hn this).trans (hf _ this hb)

lemma antitoneOn_of_succ_le (hs : s.OrdConnected)
    (hf : ∀ a, a ∈ s → succ a ∈ s → f (succ a) ≤ f a) : AntitoneOn f s :=
  monotoneOn_of_le_succ (β := βᵒᵈ) hs hf

lemma strictMonoOn_of_lt_succ (hs : s.OrdConnected)
    (hf : ∀ a, a ∈ s → succ a ∈ s → f a < f (succ a)) : StrictMonoOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  clear hab
  induction' n with n hn
  · simpa using hf _ ha hb
  rw [Function.iterate_succ_apply'] at hb ⊢
  have : succ^[n + 1] a ∈ s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
  exact (hn this).trans (hf _ this hb)

lemma strictAntiOn_of_succ_lt (hs : s.OrdConnected)
    (hf : ∀ a, a ∈ s → succ a ∈ s → f (succ a) < f a) : StrictAntiOn f s :=
  strictMonoOn_of_lt_succ (β := βᵒᵈ) hs hf

lemma monotone_of_le_succ (hf : ∀ a, f a ≤ f (succ a)) : Monotone f := by
  simpa using monotoneOn_of_le_succ Set.ordConnected_univ (by simpa using hf)

lemma antitone_of_succ_le (hf : ∀ a, f (succ a) ≤ f a) : Antitone f := by
  simpa using antitoneOn_of_succ_le Set.ordConnected_univ (by simpa using hf)

lemma strictMono_of_lt_succ (hf : ∀ a, f a < f (succ a)) : StrictMono f := by
  simpa using strictMonoOn_of_lt_succ Set.ordConnected_univ (by simpa using hf)

lemma strictAnti_of_succ_lt (hf : ∀ a, f (succ a) < f a) : StrictAnti f := by
  simpa using strictAntiOn_of_succ_lt Set.ordConnected_univ (by simpa using hf)
