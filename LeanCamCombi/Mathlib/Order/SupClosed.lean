import Mathlib.Data.Set.Finite
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.SupClosed
import LeanCamCombi.Mathlib.Data.Finset.Lattice

open OrderDual

variable {α β : Type*}

/-! ### Closure -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] {s t : Set α} {a b : α}

open Finset

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

@[simp] lemma infClosure_prod (s : Set α) (t : Set β) :
    infClosure (s ×ˢ t) = infClosure s ×ˢ infClosure t :=
  le_antisymm (infClosure_min (Set.prod_mono subset_infClosure subset_infClosure) $
    infClosed_infClosure.prod infClosed_infClosure) $ by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prod_mk_inf'_inf']

end SemilatticeInf

section DistribLattice
variable [DistribLattice α] [DistribLattice β] {s : Set α}

open Finset

@[simp] lemma latticeClosure_prod (s : Set α) (t : Set β) :
    latticeClosure (s ×ˢ t) = latticeClosure s ×ˢ latticeClosure t := by
  simp_rw [←supClosure_infClosure]; simp

end DistribLattice
