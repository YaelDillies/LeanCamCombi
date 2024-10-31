import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.StacksAttribute


variable {α β} [TopologicalSpace α] [TopologicalSpace β] (f : α → β)

def IsRetroCompact (s : Set α) : Prop := ∀ ⦃U⦄, IsCompact U → IsOpen U → IsCompact (s ∩ U)

lemma IsRetroCompact.isCompact [CompactSpace α] {s : Set α} (hs : IsRetroCompact s) :
    IsCompact s := by
  simpa using hs CompactSpace.isCompact_univ

def IsConstructible (s : Set α) : Prop := sorry

lemma IsRetroCompact.isConstructible {s : Set α} (hs : IsRetroCompact s)
    (hs' : IsOpen s) : IsConstructible s := sorry

lemma IsConstructible.union {s t : Set α} (hs : IsConstructible s)
    (ht : IsConstructible t) : IsConstructible (s ∪ t) := sorry

@[stacks 09YD]
lemma IsConstructible.image_of_isOpenEmbedding {s : Set α} (hs : IsConstructible s)
    (hf : IsOpenEmbedding f) (hf' : IsRetroCompact (Set.range f)) : IsConstructible (f '' s) :=
  sorry

@[stacks 005J]
lemma IsConstructible.preimage_of_isOpenEmbedding {s : Set β} (hs : IsConstructible s)
    (hf : IsOpenEmbedding f) : IsConstructible (f ⁻¹' s) :=
  sorry

@[stacks 09YG]
lemma IsConstructible.image_of_isClosedEmbedding {s : Set α} (hs : IsConstructible s)
    (hf : IsClosedEmbedding f) (hf' : IsRetroCompact (Set.range f)ᶜ) : IsConstructible (f '' s) :=
  sorry

@[stacks 09YE]
lemma IsConstructible.preimage_of_isClosedEmbedding {s : Set β} (hs : IsConstructible s)
    (hf : IsClosedEmbedding f) (hf' : IsCompact (Set.range f)ᶜ) : IsConstructible (f ⁻¹' s) :=
  sorry

variable {ι} (b : ι → Set α) (hb : TopologicalSpace.IsTopologicalBasis (Set.range b))

include hb in
lemma isRetroCompact_iff_isCompact_of_isTopologicalBasis [CompactSpace α]
    (hb' : ∀ i j, IsCompact (b i ∩ b j))
    {U : Set α} (hU : IsOpen U) :
    IsRetroCompact U ↔ IsCompact U := by
  refine ⟨IsRetroCompact.isCompact, fun hU' {V} hV' hV ↦ ?_⟩
  have hb'' : ∀ i, IsCompact (b i) := fun i ↦ by simpa using hb' i i
  obtain ⟨s, hs, rfl⟩ :=
    (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b hb hb'' U).mp ⟨hU', hU⟩
  obtain ⟨t, ht, rfl⟩ :=
    (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b hb hb'' V).mp ⟨hV', hV⟩
  simp only [Set.iUnion_inter, Set.inter_iUnion]
  exact ht.isCompact_biUnion fun _ _ ↦ hs.isCompact_biUnion fun _ _ ↦ (hb' _ _)

include hb in
lemma IsConstructible.induction_of_isTopologicalBasis
    (P : Set α → Prop)
    (hP : ∀ i s, Set.Finite s → P (b i \ ⋃ j ∈ s, b j))
    (hP' : ∀ s t, P s → P t → P (s ∪ t))
    (s : Set α) (hs : IsConstructible s) : P s := sorry
