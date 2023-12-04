import Mathlib.Data.Finset.Basic

variable {α : Type*} [DecidableEq α] {s t : Finset α} {a b : α}

namespace Finset

protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

lemma disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.erase a) (insert a t) ↔ Disjoint s t := by
  rw [disjoint_erase_comm, erase_insert ha]

lemma disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.erase a) ↔ Disjoint s t := by
  rw [← disjoint_erase_comm, erase_insert ha]

lemma insert_sdiff_insert' (hab : a ≠ b) (ha : a ∉ s) : insert a s \ insert b s = {a} := by
  ext; aesop

lemma erase_sdiff_erase (hab : a ≠ b) (hb : b ∈ s) : s.erase a \ s.erase b = {b} := by
  ext; aesop

lemma cons_sdiff_cons (hab : a ≠ b) (ha hb) : s.cons a ha \ s.cons b hb = {a} := by
  rw [cons_eq_insert, cons_eq_insert, insert_sdiff_insert' hab ha]

@[simp] lemma erase_nonempty (ha : a ∈ s) : (s.erase a).Nonempty ↔ s.Nontrivial := by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ ∈ _)]
  refine ⟨?_, fun hs ↦ hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

end Finset
