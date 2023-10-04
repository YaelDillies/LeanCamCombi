import Mathlib.Data.Finset.Lattice

-- attribute [protected] Finset.sup_le
-- attribute [protected] Finset.inf_le
-- attribute [protected] Finset.inf_eq_top_iff

namespace Finset
variable {ι κ α β : Type*}

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] {s : Finset ι} {t : Finset κ}

/-- See also `Finset.sup'_prod_map`. -/
lemma prod_mk_sup'_sup' (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    (sup' s hs f, sup' t ht g) = sup' (s ×ˢ t) (hs.product ht) (Prod.map f g) :=
  eq_of_forall_ge_iff λ a ↦ by
    simp only [Prod_map, sup'_le_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨by aesop, λ h ↦ ⟨λ i hi ↦ (h _ _ hi hb).1, λ j hj ↦ (h _ _ ha hj).2⟩⟩

/-- See also `Finset.prod_mk_sup'_sup'`. -/
@[simp] lemma sup'_prod_map (hst : (s ×ˢ t).Nonempty) (f : ι → α) (g : κ → β) :
    sup' (s ×ˢ t) hst (Prod.map f g) = (sup' s hst.fst f, sup' t hst.snd g) :=
  (prod_mk_sup'_sup' _ _ _ _).symm

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β] {s : Finset ι} {t : Finset κ}

/-- See also `Finset.inf'_prod_map`. -/
lemma prod_mk_inf'_inf' (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    (inf' s hs f, inf' t ht g) = inf' (s ×ˢ t) (hs.product ht) (Prod.map f g) :=
  eq_of_forall_le_iff λ a ↦ by
    simp only [Prod_map, le_inf'_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨by aesop, λ h ↦ ⟨λ i hi ↦ (h _ _ hi hb).1, λ j hj ↦ (h _ _ ha hj).2⟩⟩

/-- See also `Finset.prod_mk_inf'_inf'`. -/
@[simp] lemma inf'_prod_map (hst : (s ×ˢ t).Nonempty) (f : ι → α) (g : κ → β) :
    inf' (s ×ˢ t) hst (Prod.map f g) = (inf' s hst.fst f, inf' t hst.snd g) :=
  (prod_mk_inf'_inf' _ _ _ _).symm

end SemilatticeInf

@[elab_as_elim]
protected lemma family_induction_on {p : Finset (Finset α) → Prop} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (image_insert : ∀ (a : α) (𝒜 : Finset (Finset α)),
      (∀ s ∈ 𝒜, a ∉ s) → p 𝒜 → p (𝒜.image $ insert a))
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.filter (a ∉ ·)) → p (𝒜.filter (a ∈ ·)) → p 𝒜) :
    p 𝒜 := by
  set u := 𝒜.sup id
  have hu : ∀ s ∈ 𝒜, s ⊆ u := fun s ↦ le_sup (f := id)
  clear_value u
  induction' u using Finset.induction with a u _ ih generalizing 𝒜
  · simp_rw [subset_empty] at hu
    rw [←subset_singleton_iff', subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  refine subfamily a (ih _ ?_) ?_
  · simp only [not_not, mem_filter, and_imp]
    exact fun s hs has ↦ (subset_insert_iff_of_not_mem has).1 $ hu _ hs
  · have := image_insert a ((𝒜.filter (a ∈ ·)).image (erase · a))
      (forall_image.2 fun s _ ↦ not_mem_erase _ _)
      (ih _ $ forall_image.2 fun s hs ↦ subset_insert_iff.1 $ hu _ $ filter_subset _ _ hs)
    rwa [image_image, Finset.image_congr, image_id] at this
    rintro s hs
    exact insert_erase $ (mem_filter.1 hs).2

end Finset
