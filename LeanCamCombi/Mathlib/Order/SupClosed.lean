import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.SupClosed

variable {ι : Sort*} {α : Type*}

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] {f : ι → α} {s t : Set α}

lemma SupClosed.iSup_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : SupClosed s) (hf : ∀ i, f i ∈ s) :
    ⨆ i, f i ∈ s := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup'_univ_eq_ciSup]
  exact hs.finsetSup'_mem Finset.univ_nonempty fun _ _ ↦ hf _

lemma InfClosed.iInf_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : InfClosed s) (hf : ∀ i, f i ∈ s) :
    ⨅ i, f i ∈ s := hs.dual.iSup_mem_of_nonempty hf

lemma SupClosed.sSup_mem_of_nonempty (hs : SupClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t ⊆ s) : sSup t ∈ s := by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (by simpa)

lemma InfClosed.sInf_mem_of_nonempty (hs : InfClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t ⊆ s) : sInf t ∈ s := hs.dual.sSup_mem_of_nonempty ht ht' hts

end ConditionallyCompleteLattice

variable [CompleteLattice α] {f : ι → α} {s t : Set α}

lemma SupClosed.biSup_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [← sSup_image]
  exact hs.sSup_mem_of_nonempty (ht.image _) (by simpa) (by simpa)

lemma InfClosed.biInf_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι → α} (hs : InfClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) : ⨅ i ∈ t, f i ∈ s :=
  hs.dual.biSup_mem_of_nonempty ht ht' hf

lemma SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hbot : ⊥ ∈ s) (hf : ∀ i, f i ∈ s) :
    ⨆ i, f i ∈ s := by
  cases isEmpty_or_nonempty ι
  · simpa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty hf

lemma InfClosed.iInf_mem [Finite ι] (hs : InfClosed s) (htop : ⊤ ∈ s) (hf : ∀ i, f i ∈ s) :
    ⨅ i, f i ∈ s := hs.dual.iSup_mem htop hf

lemma SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ ∈ s) (hts : t ⊆ s) :
    sSup t ∈ s := by
  have := ht.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem hbot (by simpa)

lemma InfClosed.sInf_mem (hs : InfClosed s) (ht : t.Finite) (htop : ⊤ ∈ s) (hts : t ⊆ s) :
    sInf t ∈ s := hs.dual.sSup_mem ht htop hts

lemma SupClosed.biSup_mem {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (hbot : ⊥ ∈ s) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  have := ht.to_subtype
  rw [← sSup_image]
  exact hs.sSup_mem (ht.image _) hbot (by simpa)

lemma InfClosed.biInf_mem {ι : Type*} {t : Set ι} {f : ι → α} (hs : InfClosed s)
    (ht : t.Finite) (htop : ⊤ ∈ s) (hf : ∀ i ∈ t, f i ∈ s) : ⨅ i ∈ t, f i ∈ s :=
  hs.dual.biSup_mem ht htop hf
