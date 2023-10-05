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
end Finset
