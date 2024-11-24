import Mathlib.Order.Monotone.Monovary
import Mathlib.SetTheory.Cardinal.Basic

open Function Set

variable {ι ι' α β γ : Type*}

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
  monotone_iff_forall_lt.2 fun _a _b hab => h <| hf hab

theorem StrictMono.trans_antivary (hf : StrictMono f) (h : Antivary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun _a _b hab => h <| hf hab

theorem StrictAnti.trans_monovary (hf : StrictAnti f) (h : Monovary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun _a _b hab => h <| hf hab

theorem StrictAnti.trans_antivary (hf : StrictAnti f) (h : Antivary g f) : Monotone g :=
  monotone_iff_forall_lt.2 fun _a _b hab => h <| hf hab

theorem StrictMonoOn.trans_monovaryOn (hf : StrictMonoOn f s) (h : MonovaryOn g f s) :
    MonotoneOn g s :=
  monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb <| hf ha hb hab

theorem StrictMonoOn.trans_antivaryOn (hf : StrictMonoOn f s) (h : AntivaryOn g f s) :
    AntitoneOn g s :=
  antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb <| hf ha hb hab

theorem StrictAntiOn.trans_monovaryOn (hf : StrictAntiOn f s) (h : MonovaryOn g f s) :
    AntitoneOn g s :=
  antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha <| hf ha hb hab

theorem StrictAntiOn.trans_antivaryOn (hf : StrictAntiOn f s) (h : AntivaryOn g f s) :
    MonotoneOn g s :=
  monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha <| hf ha hb hab

end PartialOrder

end Preorder
