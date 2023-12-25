import Order.Monotone.Monovary
import SetTheory.Ordinal.Basic

#align_import mathlib.order.monotone.monovary

open Function Set

variable {ι ι' α β γ : Type _}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s t : Set ι}

theorem monovaryOn_iff_monovary : MonovaryOn f g s ↔ Monovary (fun i : s => f i) fun i => g i := by
  simp [Monovary, MonovaryOn]

theorem antivaryOn_iff_antivary : AntivaryOn f g s ↔ Antivary (fun i : s => f i) fun i => g i := by
  simp [Antivary, AntivaryOn]

section PartialOrder

variable [PartialOrder ι]

theorem StrictMono.trans_monovary (hf : StrictMono f) (h : Monovary g f) : Monotone g :=
  monotone_iff_forall_lt.2 fun a b hab => h <| hf hab

theorem StrictMono.trans_antivary (hf : StrictMono f) (h : Antivary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun a b hab => h <| hf hab

theorem StrictAnti.trans_monovary (hf : StrictAnti f) (h : Monovary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun a b hab => h <| hf hab

theorem StrictAnti.trans_antivary (hf : StrictAnti f) (h : Antivary g f) : Monotone g :=
  monotone_iff_forall_lt.2 fun a b hab => h <| hf hab

theorem StrictMonoOn.trans_monovaryOn (hf : StrictMonoOn f s) (h : MonovaryOn g f s) :
    MonotoneOn g s :=
  monotoneOn_iff_forall_lt.2 fun a ha b hb hab => h ha hb <| hf ha hb hab

theorem StrictMonoOn.trans_antivaryOn (hf : StrictMonoOn f s) (h : AntivaryOn g f s) :
    AntitoneOn g s :=
  antitoneOn_iff_forall_lt.2 fun a ha b hb hab => h ha hb <| hf ha hb hab

theorem StrictAntiOn.trans_monovaryOn (hf : StrictAntiOn f s) (h : MonovaryOn g f s) :
    AntitoneOn g s :=
  antitoneOn_iff_forall_lt.2 fun a ha b hb hab => h hb ha <| hf ha hb hab

theorem StrictAntiOn.trans_antivaryOn (hf : StrictAntiOn f s) (h : AntivaryOn g f s) :
    MonotoneOn g s :=
  monotoneOn_iff_forall_lt.2 fun a ha b hb hab => h hb ha <| hf ha hb hab

end PartialOrder

end Preorder

section

variable [LinearOrder α] [LinearOrder β] (f : ι → α) (g : ι → β) {s : Set ι}

/-- If `f : ι → α` and `g : ι → β` are monovarying, then `monovary_order f g` is a linear order on
`ι` that makes `f` and `g` simultaneously monotone.
We define `i < j` if `f i < f j`, or if `f i = f j` and `g i < g j`, breaking ties arbitrarily. -/
def MonovaryOrder (i j : ι) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel) (f i, g i, i) (f j, g j, j)

instance : IsStrictTotalOrder ι (MonovaryOrder f g)
    where
  trichotomous i j :=
    by
    convert trichotomous_of (Prod.Lex (· < ·) <| Prod.Lex (· < ·) WellOrderingRel) _ _
    · simp only [Prod.ext_iff, ← and_assoc', imp_and, eq_iff_iff, iff_and_self]
      exact ⟨congr_arg _, congr_arg _⟩
    · infer_instance
  irrefl i := by rw [MonovaryOrder]; exact irrefl _
  trans i j k := by rw [MonovaryOrder]; exact trans

variable {f g}

theorem monovaryOn_iff_exists_monotoneOn :
    MonovaryOn f g s ↔ ∃ (_ : LinearOrder ι), MonotoneOn f s ∧ MonotoneOn g s := by
  classical
  letI := linearOrderOfSTO (MonovaryOrder f g)
  refine'
    ⟨fun hfg =>
      ⟨‹_›, monotoneOn_iff_forall_lt.2 fun i hi j hj hij => _,
        monotoneOn_iff_forall_lt.2 fun i hi j hj hij => _⟩,
      _⟩
  · obtain h | ⟨h, -⟩ := Prod.lex_iff.1 hij <;> exact h.le
  · obtain h | ⟨-, h⟩ := Prod.lex_iff.1 hij
    · exact hfg.symm hi hj h
    obtain h | ⟨h, -⟩ := Prod.lex_iff.1 h <;> exact h.le
  · rintro ⟨_, hf, hg⟩
    exact hf.monovary_on hg

theorem antivaryOn_iff_exists_monotoneOn_antitoneOn :
    AntivaryOn f g s ↔ ∃ (_ : LinearOrder ι), MonotoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← monovaryOn_toDual_right, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

theorem monovaryOn_iff_exists_antitoneOn :
    MonovaryOn f g s ↔ ∃ (_ : LinearOrder ι), AntitoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← antivaryOn_toDual_left, antivaryOn_iff_exists_monotoneOn_antitoneOn,
    monotoneOn_toDual_comp_iff]

theorem antivaryOn_iff_exists_antitoneOn_monotoneOn :
    AntivaryOn f g s ↔ ∃ (_ : LinearOrder ι), AntitoneOn f s ∧ MonotoneOn g s := by
  simp_rw [← monovaryOn_toDual_left, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

theorem monovary_iff_exists_monotone :
    Monovary f g ↔ ∃ (_ : LinearOrder ι), Monotone f ∧ Monotone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_monotoneOn]

theorem antivary_iff_exists_monotone_antitone :
    Antivary f g ↔ ∃ (_ : LinearOrder ι), Monotone f ∧ Antitone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_monotoneOn_antitoneOn]

theorem monovary_iff_exists_antitone :
    Monovary f g ↔ ∃ (_ : LinearOrder ι), Antitone f ∧ Antitone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_antitoneOn]

theorem antivary_iff_exists_antitone_monotone :
    Antivary f g ↔ ∃ (_ : LinearOrder ι), Antitone f ∧ Monotone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_antitoneOn_monotoneOn]

alias ⟨MonovaryOn.exists_monotoneOn, _⟩ := monovaryOn_iff_exists_monotoneOn

alias ⟨AntivaryOn.exists_monotoneOn_antitoneOn, _⟩ := antivaryOn_iff_exists_monotoneOn_antitoneOn

alias ⟨MonovaryOn.exists_antitoneOn, _⟩ := monovaryOn_iff_exists_antitoneOn

alias ⟨AntivaryOn.exists_antitoneOn_monotoneOn, _⟩ := antivaryOn_iff_exists_antitoneOn_monotoneOn

alias ⟨Monovary.exists_monotone, _⟩ := monovary_iff_exists_monotone

alias ⟨Antivary.exists_monotone_antitone, _⟩ := antivary_iff_exists_monotone_antitone

alias ⟨Monovary.exists_antitone, _⟩ := monovary_iff_exists_antitone

alias ⟨Antivary.exists_antitone_monotone, _⟩ := antivary_iff_exists_antitone_monotone

end

