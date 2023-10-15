import Mathlib.Data.Set.Finite
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.SupClosed
import LeanCamCombi.Mathlib.Data.Finset.Lattice
import LeanCamCombi.Mathlib.Order.Closure

open OrderDual

variable {ι : Sort*} {F α β : Type*}

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] {s t : Set α} {a b : α}

lemma SupClosed.preimage [SupHomClass F β α] (hs : SupClosed s) (f : F) : SupClosed (f ⁻¹' s) :=
  fun a ha b hb ↦ by simpa [map_sup] using hs ha hb

lemma SupClosed.image [SupHomClass F α β] (hs : SupClosed s) (f : F) : SupClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [←map_sup]
  exact Set.mem_image_of_mem _ $ hs ha hb

lemma supClosed_range [SupHomClass F α β] (f : F) : SupClosed (Set.range f) := by
  simpa using supClosed_univ.image f

lemma SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ×ˢ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma supClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, SemilatticeSup (α i)] {s : Set ι}
  {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, SupClosed (t i)) : SupClosed (s.pi t) :=
  fun _a ha _b hb _i hi ↦ ht _ hi (ha _ hi) (hb _ hi)

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β] {s t : Set α} {a b : α}

lemma InfClosed.preimage [InfHomClass F β α] (hs : InfClosed s) (f : F) : InfClosed (f ⁻¹' s) :=
  fun a ha b hb ↦ by simpa [map_inf] using hs ha hb

lemma InfClosed.image [InfHomClass F α β] (hs : InfClosed s) (f : F) : InfClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [←map_inf]
  exact Set.mem_image_of_mem _ $ hs ha hb

lemma infClosed_range [InfHomClass F α β] (f : F) : InfClosed (Set.range f) := by
  simpa using infClosed_univ.image f

lemma InfClosed.prod {t : Set β} (hs : InfClosed s) (ht : InfClosed t) : InfClosed (s ×ˢ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma infClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, SemilatticeInf (α i)] {s : Set ι}
  {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, InfClosed (t i)) : InfClosed (s.pi t) :=
  fun _a ha _b hb _i hi ↦ ht _ hi (ha _ hi) (hb _ hi)

end SemilatticeInf

section Lattice
variable [Lattice α] [Lattice β] {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}

open Set

/-- A set `s` is *lattice-closed* if `a ⊔ b ∈ s` and `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
structure LatticeClosed (s : Set α) : Prop where
  supClosed : SupClosed s
  infClosed : InfClosed s

@[simp] lemma latticeClosed_empty : LatticeClosed (∅ : Set α) := ⟨supClosed_empty, infClosed_empty⟩
@[simp] lemma latticeClosed_singleton : LatticeClosed ({a} : Set α) :=
  ⟨supClosed_singleton, infClosed_singleton⟩

@[simp] lemma latticeClosed_univ : LatticeClosed (Set.univ : Set α) :=
  ⟨supClosed_univ, infClosed_univ⟩

lemma LatticeClosed.inter (hs : LatticeClosed s) (ht : LatticeClosed t) : LatticeClosed (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

lemma latticeClosed_sInter (hS : ∀ s ∈ S, LatticeClosed s) : LatticeClosed (⋂₀ S) :=
  ⟨supClosed_sInter fun _s hs ↦ (hS _ hs).1, infClosed_sInter fun _s hs ↦ (hS _ hs).2⟩

lemma latticeClosed_iInter (hf : ∀ i, LatticeClosed (f i)) : LatticeClosed (⋂ i, f i) :=
  ⟨supClosed_iInter fun _i ↦ (hf _).1, infClosed_iInter fun _i ↦ (hf _).2⟩

@[simp] lemma latticeClosed_preimage_toDual {s : Set αᵒᵈ} :
    LatticeClosed (toDual ⁻¹' s) ↔ LatticeClosed s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

@[simp] lemma latticeClosed_preimage_ofDual :
    LatticeClosed (ofDual ⁻¹' s) ↔ LatticeClosed s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

alias ⟨_, LatticeClosed.dual⟩ := latticeClosed_preimage_ofDual
alias ⟨_, LatticeClosed.of_dual⟩ := latticeClosed_preimage_toDual

lemma LatticeClosed.preimage [LatticeHomClass F β α] (hs : LatticeClosed s) (f : F) :
    LatticeClosed (f ⁻¹' s) :=
  ⟨hs.1.preimage _, hs.2.preimage _⟩

lemma LatticeClosed.image [LatticeHomClass F α β] (hs : LatticeClosed s) (f : F) :
    LatticeClosed (f '' s) :=
  ⟨hs.1.image _, hs.2.image _⟩

lemma LatticeClosed_range [LatticeHomClass F α β] (f : F) : LatticeClosed (Set.range f) :=
  ⟨supClosed_range _, infClosed_range _⟩

lemma LatticeClosed.prod {t : Set β} (hs : LatticeClosed s) (ht : LatticeClosed t) :
    LatticeClosed (s ×ˢ t) := ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

lemma latticeClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)] {s : Set ι}
  {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, LatticeClosed (t i)) : LatticeClosed (s.pi t) :=
  ⟨supClosed_pi fun _i hi ↦ (ht _ hi).1, infClosed_pi fun _i hi ↦ (ht _ hi).2⟩

end Lattice

section LinearOrder
variable [LinearOrder α]

@[simp] protected lemma LinearOrder.latticeClosed (s : Set α) : LatticeClosed s :=
  ⟨LinearOrder.supClosed _, LinearOrder.infClosed _⟩

end LinearOrder

/-! ### Closure -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] {s t : Set α} {a b : α}

open Finset

lemma sup_mem_supClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊔ b ∈ supClosure s :=
  supClosed_supClosure (subset_supClosure ha) (subset_supClosure hb)

lemma finsetSup'_mem_supClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ supClosure s :=
  supClosed_supClosure.finsetSup'_mem _ $ fun _i hi ↦ subset_supClosure $ hf _ hi

@[simp] lemma supClosure_closed : supClosure.closed = {s : Set α | SupClosed s} := by
  ext; exact ClosureOperator.mem_mk₃_closed

lemma supClosure_min (hst : s ⊆ t) (ht : SupClosed t) : supClosure s ⊆ t :=
  ClosureOperator.closure_le_mk₃_iff hst ht

/-- The semilatice generated by a finite set is finite. -/
protected lemma Set.Finite.supClosure (hs : s.Finite) : (supClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine' ((s.powerset.filter Finset.Nonempty).attach.image
    fun t ↦ t.1.sup' (mem_filter.1 t.2).2 id).finite_toSet.subset _
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩

@[simp] lemma supClosure_prod (s : Set α) (t : Set β) :
    supClosure (s ×ˢ t) = supClosure s ×ˢ supClosure t :=
  le_antisymm (supClosure_min (Set.prod_mono subset_supClosure subset_supClosure) $
    supClosed_supClosure.prod supClosed_supClosure) $ by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prod_mk_sup'_sup']

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β] {s t : Set α} {a b : α}

open Finset

lemma inf_mem_infClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊓ b ∈ infClosure s :=
  infClosed_infClosure (subset_infClosure ha) (subset_infClosure hb)

lemma finsetInf'_mem_infClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.inf' ht f ∈ infClosure s :=
  infClosed_infClosure.finsetInf'_mem _ $ fun _i hi ↦ subset_infClosure $ hf _ hi

@[simp] lemma infClosure_closed : infClosure.closed = {s : Set α | InfClosed s} := by
  ext; exact ClosureOperator.mem_mk₃_closed

lemma infClosure_min (hst : s ⊆ t) (ht : InfClosed t) : infClosure s ⊆ t :=
  ClosureOperator.closure_le_mk₃_iff hst ht

/-- The semilatice generated by a finite set is finite. -/
protected lemma Set.Finite.infClosure (hs : s.Finite) : (infClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine' ((s.powerset.filter Finset.Nonempty).attach.image
    fun t ↦ t.1.inf' (mem_filter.1 t.2).2 id).finite_toSet.subset _
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩

@[simp] lemma infClosure_prod (s : Set α) (t : Set β) :
    infClosure (s ×ˢ t) = infClosure s ×ˢ infClosure t :=
  le_antisymm (infClosure_min (Set.prod_mono subset_infClosure subset_infClosure) $
    infClosed_infClosure.prod infClosed_infClosure) $ by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prod_mk_inf'_inf']

end SemilatticeInf

section Lattice
variable [Lattice α] {s t : Set α}

/-- Every set in a join-semilattice generates a set closed under join. -/
def latticeClosure : ClosureOperator (Set α) :=
  ClosureOperator.ofPred LatticeClosed $ fun _ ↦ latticeClosed_sInter

@[simp] lemma subset_latticeClosure : s ⊆ latticeClosure s := latticeClosure.le_closure _

@[simp] lemma latticeClosed_latticeClosure : LatticeClosed (latticeClosure s) :=
  ClosureOperator.ofPred_spec _

lemma latticeClosure_min (hst : s ⊆ t) (ht : LatticeClosed t) : latticeClosure s ⊆ t := by
  rw [latticeClosure, ClosureOperator.ofPred]
  exact ClosureOperator.closure_le_mk₃_iff hst ht

lemma latticeClosure_mono : Monotone (latticeClosure : Set α → Set α) := latticeClosure.monotone

@[simp] lemma latticeClosure_eq_self : latticeClosure s = s ↔ LatticeClosed s :=
  ClosureOperator.mem_closed_ofPred

@[simp] lemma latticeClosure_closed : latticeClosure.closed = {s : Set α | LatticeClosed s} :=
  ClosureOperator.closed_ofPred

alias ⟨_, LatticeClosed.latticeClosure_eq⟩ := latticeClosure_eq_self

lemma latticeClosure_idem (s : Set α) : latticeClosure (latticeClosure s) = latticeClosure s :=
  latticeClosure.idempotent _

@[simp] lemma latticeClosure_empty : latticeClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma latticeClosure_singleton (a : α) : latticeClosure {a} = {a} := by simp
@[simp] lemma latticeClosure_univ : latticeClosure (Set.univ : Set α) = Set.univ := by simp

end Lattice

section DistribLattice
variable [DistribLattice α] [DistribLattice β] {s : Set α}

open Finset

protected lemma SupClosed.infClosure (hs : SupClosed s) : SupClosed (infClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [inf'_sup_inf']
  exact finsetInf'_mem_infClosure _
    fun i hi ↦ hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

protected lemma InfClosed.supClosure (hs : InfClosed s) : InfClosed (supClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [sup'_inf_sup']
  exact finsetSup'_mem_supClosure _
    fun i hi ↦ hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

@[simp] lemma supClosure_infClosure (s : Set α) : supClosure (infClosure s) = latticeClosure s :=
  le_antisymm (supClosure_min (infClosure_min subset_latticeClosure latticeClosed_latticeClosure.2)
    latticeClosed_latticeClosure.1) $ latticeClosure_min (subset_infClosure.trans subset_supClosure)
      ⟨supClosed_supClosure, infClosed_infClosure.supClosure⟩

@[simp] lemma infClosure_supClosure (s : Set α) : infClosure (supClosure s) = latticeClosure s :=
  le_antisymm (infClosure_min (supClosure_min subset_latticeClosure latticeClosed_latticeClosure.1)
    latticeClosed_latticeClosure.2) $ latticeClosure_min (subset_supClosure.trans subset_infClosure)
      ⟨supClosed_supClosure.infClosure, infClosed_infClosure⟩

lemma Set.Finite.latticeClosure (hs : s.Finite) : (latticeClosure s).Finite := by
  rw [←supClosure_infClosure]; exact hs.infClosure.supClosure

@[simp] lemma latticeClosure_prod (s : Set α) (t : Set β) :
    latticeClosure (s ×ˢ t) = latticeClosure s ×ˢ latticeClosure t := by
  simp_rw [←supClosure_infClosure]; simp

end DistribLattice
