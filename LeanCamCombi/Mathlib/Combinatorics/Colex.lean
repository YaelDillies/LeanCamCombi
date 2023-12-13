import Mathlib.Combinatorics.Colex
import LeanCamCombi.Mathlib.Data.Finset.Basic

variable {α β : Type*}

namespace Finset
namespace Colex
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α}

lemma cons_le_cons (ha hb) : toColex (s.cons a ha) ≤ toColex (s.cons b hb) ↔ a ≤ b := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [←toColex_sdiff_le_toColex_sdiff', cons_sdiff_cons hab, cons_sdiff_cons hab.symm,
   singleton_le_singleton]

lemma cons_lt_cons (ha hb) : toColex (s.cons a ha) < toColex (s.cons b hb) ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons _ _) (cons_le_cons _ _)

variable [DecidableEq α]

lemma insert_le_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) ≤ toColex (insert b s) ↔ a ≤ b := by
  rw [←cons_eq_insert _ _ ha, ←cons_eq_insert _ _ hb, cons_le_cons]

lemma insert_lt_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) < toColex (insert b s) ↔ a < b := by
  rw [←cons_eq_insert _ _ ha, ←cons_eq_insert _ _ hb, cons_lt_cons]

lemma erase_le_erase (ha : a ∈ s) (hb : b ∈ s) :
    toColex (s.erase a) ≤ toColex (s.erase b) ↔ b ≤ a := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [←toColex_sdiff_le_toColex_sdiff', erase_sdiff_erase hab hb, erase_sdiff_erase hab.symm ha,
   singleton_le_singleton]

lemma erase_lt_erase (ha : a ∈ s) (hb : b ∈ s) :
    toColex (s.erase a) < toColex (s.erase b) ↔ b < a :=
  lt_iff_lt_of_le_iff_le' (erase_le_erase hb ha) (erase_le_erase ha hb)

end PartialOrder

section LinearOrder
variable [LinearOrder α] {s t : Finset α} {a : α}

instance [Fintype α] : BoundedOrder (Colex α) where
  top := toColex univ
  le_top _x := toColex_le_toColex_of_subset $ subset_univ _

@[simp] lemma toColex_univ [Fintype α] : toColex (univ : Finset α) = ⊤ := rfl
@[simp] lemma ofColex_top [Fintype α] : ofColex (⊤ : Colex α) = univ := rfl

lemma lt_iff_exists_forall_lt_mem_iff_mem :
    toColex s < toColex t ↔ ∃ w ∈ t, w ∉ s ∧ ∀ ⦃a⦄, w < a → (a ∈ s ↔ a ∈ t) := by
  simp only [lt_iff_exists_forall_lt]
  refine ⟨fun h ↦ ?_, ?_⟩
  · let u := (t \ s).filter fun w ↦ ∀ a ∈ s, a ∉ t → a < w
    have mem_u {w : α} : w ∈ u ↔ w ∈ t ∧ w ∉ s ∧ ∀ a ∈ s, a ∉ t → a < w := by simp [and_assoc]
    have hu : u.Nonempty := h.imp fun _ ↦ mem_u.2
    let m := max' _ hu
    have ⟨hmt, hms, hm⟩ : m ∈ t ∧ m ∉ s ∧ ∀ a ∈ s, a ∉ t → a < m := mem_u.1 $ max'_mem _ _
    refine ⟨m, hmt, hms, fun a hma ↦ ⟨fun has ↦ not_imp_comm.1 (hm _ has) hma.asymm, fun hat ↦ ?_⟩⟩
    by_contra has
    have hau : a ∈ u := mem_u.2 ⟨hat, has, fun b hbs hbt ↦ (hm _ hbs hbt).trans hma⟩
    exact hma.not_le $ le_max' _ _ hau
  · rintro ⟨w, hwt, hws, hw⟩
    refine ⟨w, hwt, hws, fun a has hat ↦ ?_⟩
    by_contra! hwa
    exact hat $ (hw $ hwa.lt_of_ne $ ne_of_mem_of_not_mem hwt hat).1 has

lemma erase_le_erase_min' (hst : toColex s ≤ toColex t) (hcard : s.card ≤ t.card) (ha : a ∈ s) :
    toColex (s.erase a) ≤
      toColex (t.erase $ min' t $ card_pos.1 $ (card_pos.2 ⟨a, ha⟩).trans_le hcard) := by
  generalize_proofs ht
  set m := min' t ht
  -- Case on whether `s = t`
  obtain rfl | h' := eq_or_ne s t
  -- If `s = t`, then `s \ {a} ≤ s \ {m}` because `m ≤ a`
  · exact (erase_le_erase ha $ min'_mem _ _).2 $ min'_le _ _ $ ha
  -- If `s ≠ t`, call `w` the colex witness. Case on whether `w < a` or `a < w`
  replace hst := hst.lt_of_ne $ toColex_inj.not.2 h'
  simp only [lt_iff_exists_forall_lt_mem_iff_mem] at hst
  obtain ⟨w, hwt, hws, hw⟩ := hst
  obtain hwa | haw := (ne_of_mem_of_not_mem ha hws).symm.lt_or_lt
  -- If `w < a`, then `a` is the colex witness for `s \ {a} < t \ {m}`
  · have hma : m < a := (min'_le _ _ hwt).trans_lt hwa
    refine (lt_iff_exists_forall_lt.2 ⟨a, mem_erase.2 ⟨hma.ne', (hw hwa).1 ha⟩,
      not_mem_erase _ _, fun b hbs hbt ↦ ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase, not_and_or, not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hab
      exact hbt $ (hw $ hwa.trans_le hab).1 $ mem_of_mem_erase hbs
  -- If `a < w`, case on whether `m < w` or `m = w`
  obtain rfl | hmw : m = w ∨ m < w := (min'_le _ _ hwt).eq_or_lt
  -- If `m = w`, then `s \ {a} = t \ {m}`
  · have : erase t m ⊆ erase s a
    · rintro b hb
      rw [mem_erase] at hb ⊢
      exact ⟨(haw.trans_le $ min'_le _ _ hb.2).ne', (hw $ hb.1.lt_of_le' $ min'_le _ _ hb.2).2 hb.2⟩
    rw [eq_of_subset_of_card_le this]
    rw [card_erase_of_mem ha, card_erase_of_mem (min'_mem _ _)]
    exact tsub_le_tsub_right hcard _
  -- If `m < w`, then `w` works as the colex witness for  `s \ {a} < t \ {m}`
  · refine (lt_iff_exists_forall_lt.2 ⟨w, mem_erase.2 ⟨hmw.ne', hwt⟩, mt mem_of_mem_erase hws,
      fun b hbs hbt ↦ ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase, not_and_or, not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hwb
      exact hbt $ (hw $ hwb.lt_of_ne $ ne_of_mem_of_not_mem hwt hbt).1 $ mem_of_mem_erase hbs

end LinearOrder
end Colex
end Finset
