import Mathlib.Order.Sublattice
import LeanCamCombi.Mathlib.Order.Hom.Lattice

/-!
# Sublattices

This file defines sublattices.

## Main definitions

## TODO

Subsemilattices, if people care about them.

## Tags

sublattice
-/

open Function Set

variable {ι : Sort*} {α β γ : Type*} [Lattice α] [Lattice β] [Lattice γ]

namespace Sublattice
variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a : α}

def prod (L : Sublattice α) (M : Sublattice β) : Sublattice (α × β) where
  carrier := L ×ˢ M
  supClosed' := L.supClosed.prod M.supClosed
  infClosed' := L.infClosed.prod M.infClosed

@[simp, norm_cast] lemma coe_prod (L : Sublattice α) (M : Sublattice β) :
    L.prod M = (L ×ˢ M : Set (α × β)) := rfl

@[simp] lemma mem_prod {M : Sublattice β} {p : α × β} : p ∈ L.prod M ↔ p.1 ∈ L ∧ p.2 ∈ M := Iff.rfl

lemma prod_mono {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublattice β} (hL : L₁ ≤ L₂) (hM : M₁ ≤ M₂) :
    L₁.prod M₁ ≤ L₂.prod M₂ := Set.prod_mono hL hM

lemma prod_mono_right {M₁ M₂ : Sublattice β} (hM : M₁ ≤ M₂) : L.prod M₁ ≤ L.prod M₂ :=
  prod_mono le_rfl hM

lemma prod_mono_left {L₁ L₂ : Sublattice α} {M : Sublattice β} (hL : L₁ ≤ L₂) :
    L₁.prod M ≤ L₂.prod M := prod_mono hL le_rfl

lemma prod_top (L : Sublattice α) : L.prod (⊤ : Sublattice β) = L.comap (LatticeHom.fst α β) :=
  ext fun a ↦ by simp [mem_prod, LatticeHom.coe_fst]

lemma top_prod (L : Sublattice β) : (⊤ : Sublattice α).prod L = L.comap (LatticeHom.snd α β) :=
  ext fun a ↦ by simp [mem_prod, LatticeHom.coe_snd]

@[simp] lemma top_prod_top : (⊤ : Sublattice α).prod (⊤ : Sublattice β) = ⊤ :=
  (top_prod _).trans $ comap_top _

@[simp] lemma prod_bot (L : Sublattice α) : L.prod (⊥ : Sublattice β) = ⊥ :=
  SetLike.coe_injective prod_empty

@[simp] lemma bot_prod (M : Sublattice β) : (⊥ : Sublattice α).prod M = ⊥ :=
  SetLike.coe_injective empty_prod

lemma le_prod_iff {M : Sublattice β} {N : Sublattice (α × β)} :
    N ≤ L.prod M ↔ N ≤ comap (LatticeHom.fst α β) L ∧ N ≤ comap (LatticeHom.snd α β) M := by
  simp [SetLike.le_def, forall_and]

@[simp] lemma prod_eq_bot {M : Sublattice β} : L.prod M = ⊥ ↔ L = ⊥ ∨ M = ⊥ := by
  simpa only [←coe_inj] using Set.prod_eq_empty_iff

@[simp] lemma prod_eq_top [Nonempty α] [Nonempty β] {M : Sublattice β} :
    L.prod M = ⊤ ↔ L = ⊤ ∧ M = ⊤ := by simpa only [←coe_inj] using Set.prod_eq_univ

/-- The product of sublattices is isomorphic to their product as lattices. -/
def prodEquiv (L : Sublattice α) (M : Sublattice β) : L.prod M ≃o L × M where
  toEquiv := Equiv.Set.prod _ _
  map_rel_iff' := Iff.rfl

section Pi
variable {κ : Type*} {π : κ → Type*} [∀ i, Lattice (π i)]

/-- Arbitrary product of sublattices. Given an index set `s` and a family of sublattices
`L : Π i, Sublattice (α i)`, `pi s L` is the sublattice of dependent functions `f : Π i, α i` such
that `f i` belongs to `L i` whenever `i ∈ s`. -/
def pi (s : Set κ) (L : ∀ i, Sublattice (π i)) : Sublattice (∀ i, π i) where
  carrier := s.pi fun i ↦ L i
  supClosed' := supClosed_pi fun i _ ↦ (L i).supClosed
  infClosed' := infClosed_pi fun i _ ↦ (L i).infClosed

@[simp, norm_cast] lemma coe_pi (s : Set κ) (L : ∀ i, Sublattice (π i)) :
    (pi s L : Set (∀ i, π i)) = Set.pi s fun i ↦ L i := rfl

@[simp] lemma mem_pi {s : Set κ} {L : ∀ i, Sublattice (π i)} {x : ∀ i, π i} :
    x ∈ pi s L ↔ ∀ i, i ∈ s → x i ∈ L i := Iff.rfl

@[simp] lemma pi_empty (L : ∀ i, Sublattice (π i)) : pi ∅ L = ⊤ := ext fun a ↦ by simp [mem_pi]

@[simp] lemma pi_top (s : Set κ) : (pi s fun i ↦ ⊤ : Sublattice (∀ i, π i)) = ⊤ :=
  ext fun a ↦ by simp [mem_pi]

@[simp] lemma pi_bot [Nonempty κ] : (pi univ fun i ↦ ⊥ : Sublattice (∀ i, π i)) = ⊥ :=
  ext fun a ↦ by simp [mem_pi]

lemma le_pi {s : Set κ} {L : ∀ i, Sublattice (π i)} {M : Sublattice (∀ i, π i)} :
    M ≤ pi s L ↔ ∀ i ∈ s, M ≤ comap (Pi.evalLatticeHom π i) (L i) := by simp [SetLike.le_def]; aesop

@[simp] lemma pi_univ_eq_bot {L : ∀ i, Sublattice (π i)} : pi univ L = ⊥ ↔ ∃ i, L i = ⊥ := by
  simp_rw [←coe_inj]; simp

end Pi
end Sublattice

#exit

open Sublattice

namespace LatticeHom
variable [Lattice β] [Lattice γ] {L : Sublattice α} {f : LatticeHom α β} {b : β}

/-- Restriction of a lattice hom to a sublattice of the domain. -/
def restrict (f : LatticeHom α β) (L : Sublattice α) : LatticeHom L β := f.comp L.subtype

@[simp]
lemma restrict_apply (f : LatticeHom α β) (L : Sublattice α) (a : L) : f.restrict L a = f a := rfl

/-- Restriction of a lattice hom to a sublattice of the codomain. -/
def codRestrict (f : LatticeHom α β) (L : Sublattice β) (h : ∀ x, f x ∈ L) : LatticeHom α L where
  toFun := Set.codRestrict f L h
  map_sup' a b := Subtype.ext $ map_sup f a b
  map_inf' a b := Subtype.ext $ map_inf f a b

@[simp, norm_cast] lemma coe_codRestrict (f : LatticeHom α β) (L : Sublattice β) (h) :
    codRestrict f L h = Set.codRestrict f L h := rfl

lemma codRestrict_injective {L : Sublattice β} {h} :
    Injective (f.codRestrict L h) ↔ Injective f := Set.injective_codRestrict _

/-- The range of a monoid homomorphism from a lattice is a sublattice. -/
def range (f : LatticeHom α β) : Sublattice β :=
  Sublattice.copy ((⊤ : Sublattice α).map f) (Set.range f) (by simp [Set.ext_iff])

@[simp, norm_cast] lemma coe_range (f : LatticeHom α β) : (f.range : Set β) = Set.range f := rfl

@[simp] lemma mem_range : b ∈ f.range ↔ ∃ a, f a = b := Iff.rfl

@[simp] lemma map_top (f : LatticeHom α β) : (⊤ : Sublattice α).map f = f.range :=
  (Sublattice.copy_eq _ _ _).symm

lemma restrict_range (f : LatticeHom α β) : (f.restrict L).range = L.map f := by
  simp [SetLike.ext_iff]

/-- The canonical surjective lattice homomorphism `α → f(α)` induced by a lattice
homomorphism `LatticeHom α β`. -/
def rangeRestrict (f : LatticeHom α β) : LatticeHom α f.range := codRestrict f _ fun a ↦ ⟨a, rfl⟩

@[simp, norm_cast]
lemma coe_rangeRestrict (f : LatticeHom α β) (a : α) : (f.rangeRestrict a : β) = f a := rfl

@[simp] lemma coe_comp_rangeRestrict (f : LatticeHom α β) :
    ((↑) : f.range → β) ∘ (⇑f.rangeRestrict : α → f.range) = f := rfl

lemma subtype_comp_rangeRestrict (f : LatticeHom α β) : f.range.subtype.comp f.rangeRestrict = f :=
  ext $ f.coe_rangeRestrict

lemma rangeRestrict_surjective (f : LatticeHom α β) : Surjective f.rangeRestrict :=
  fun ⟨_, g, rfl⟩ ↦ ⟨g, rfl⟩

lemma rangeRestrict_injective : Injective f.rangeRestrict ↔ Injective f := codRestrict_injective

lemma map_range (g : LatticeHom β γ) (f : LatticeHom α β) : f.range.map g = (g.comp f).range := by
  simpa only [map_top] using (⊤ : Sublattice α).map_map g f

@[simp] lemma range_eq_top : f.range = (⊤ : Sublattice β) ↔ Surjective f :=
  SetLike.ext'_iff.trans Set.range_iff_surjective

/-- The range of a surjective lattice homomorphism is the whole of the codomain. -/
lemma range_eq_top_of_surjective {β} [Lattice β] (f : LatticeHom α β) (hf : Surjective f) :
    f.range = (⊤ : Sublattice β) :=
  range_eq_top.2 hf

lemma _root_.Sublattice.range_subtype (L : Sublattice α) : L.subtype.range = L := by
  rw [←map_top, ←SetLike.coe_set_eq, coe_map, Sublattice.coe_subtype]; ext; simp

/-- Computable alternative to `LatticeHom.ofInjective`. -/
def ofLeftInverse {f : LatticeHom α β} {g : β →* α} (h : LeftInverse g f) : α ≃o f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.subtype
    left_inv := h
    right_inv := by
      rintro ⟨a, y, rfl⟩
      apply Subtype.ext
      rw [coe_rangeRestrict, comp_apply, Sublattice.coeSubtype, Subtype.coe_mk, h] }

lemma ofLeftInverse_apply {f : LatticeHom α β} {g : β →* α} (h : LeftInverse g f) (a : α) :
    ↑(ofLeftInverse h a) = f a :=
  rfl

lemma ofLeftInverse_symm_apply {f : LatticeHom α β} {g : β →* α} (h : LeftInverse g f)
    (a : f.range) : (ofLeftInverse h).symm a = g a :=
  rfl

/-- The range of an injective lattice homomorphism is isomorphic to its domain. -/
noncomputable def ofInjective {f : LatticeHom α β} (hf : Injective f) : α ≃o f.range :=
  MulEquiv.ofBijective (f.codRestrict f.range fun a ↦ ⟨a, rfl⟩)
    ⟨fun a y h ↦ hf (Subtype.ext_iff.mp h), by
      rintro ⟨a, y, rfl⟩
      exact ⟨y, rfl⟩⟩

lemma ofInjective_apply {f : LatticeHom α β} (hf : Injective f) {a : α} :
    ↑(ofInjective hf a) = f a :=
  rfl

lemma apply_ofInjective_symm {f : LatticeHom α β} (hf : Injective f) (a : f.range) :
    f ((ofInjective hf).symm a) = a :=
  Subtype.ext_iff.1 $ (ofInjective hf).apply_symm_apply a

section EqLocus

variable {M : Type*} [Monoid M]

/-- The Sublattice of elements `a : α` such that `f a = g a` -/
def eqLocus (f g : α →* M) : Sublattice α :=
  { eqLocusM f g with inv_mem' := eq_on_inv f g }

lemma eqLocus_same (f : LatticeHom α β) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ ↦ eq_self_iff_true _

/-- If two monoid homomorphisms are equal on a set, then they are equal on its Sublattice closure. -/
lemma eqOn_closure {f g : α →* M} {s : Set α} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from (closure_le _).2 h

lemma eq_of_eqOn_top {f g : α →* M} (h : Set.EqOn f g (⊤ : Sublattice α)) : f = g :=
  ext fun _x ↦ h trivial

lemma eq_of_eqOn_dense {s : Set α} (hs : closure s = ⊤) {f g : α →* M} (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_top $ hs ▸ eqOn_closure h

end EqLocus

lemma closure_preimage_le (f : LatticeHom α β) (s : Set β) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  (closure_le _).2 fun a hx ↦ by rw [SetLike.mem_coe, mem_comap]; exact subset_closure hx

/-- The image under a monoid homomorphism of the Sublattice generated by a set equals the Sublattice
generated by the image of the set. -/
lemma map_closure (f : LatticeHom α β) (s : Set α) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (Sublattice.gc_map_comap f) (Sublattice.gi β).gc
    (Sublattice.gi α).gc fun _t ↦ rfl

end LatticeHom

namespace Sublattice

variable {β : Type*} [Lattice β] (L : Sublattice α)

lemma map_eq_bot_iff {f : LatticeHom α β} : L.map f = ⊥ ↔ L ≤ f.ker :=
  (gc_map_comap f).l_eq_bot

lemma map_eq_bot_iff_of_injective {f : LatticeHom α β} (hf : Injective f) :
    L.map f = ⊥ ↔ L = ⊥ := by rw [map_eq_bot_iff, f.ker_eq_bot_iff.mpr hf, le_bot_iff]

end Sublattice

namespace Sublattice

open LatticeHom

variable {β : Type*} [Lattice β] (f : LatticeHom α β)

lemma map_le_range (L : Sublattice α) : map f L ≤ f.range :=
  (range_eq_map f).symm ▸ map_mono le_top

lemma map_subtype_le (L : Sublattice L) : L.map L.subtype ≤ L :=
  (L.map_le_range L.subtype).trans (le_of_eq L.subtype_range)

lemma ker_le_comap (L : Sublattice β) : f.ker ≤ comap f L :=
  comap_bot f ▸ comap_mono bot_le

lemma map_comap_le (L : Sublattice β) : map f (comap f L) ≤ L :=
  (gc_map_comap f).l_u_le _

lemma le_comap_map (L : Sublattice α) : L ≤ comap f (map f L) :=
  (gc_map_comap f).le_u_l _

lemma map_comap_eq (L : Sublattice β) : map f (comap f L) = f.range ⊓ L :=
  SetLike.ext' $ by
    rw [coe_map, coe_comap, Set.image_preimage_eq_inter_range, coe_inf, coe_range, Set.inter_comm]

lemma comap_map_eq (L : Sublattice α) : comap f (map f L) = L ⊔ f.ker := by
  refine' le_antisymm _ (sup_le (le_comap_map _ _) (ker_le_comap _ _))
  intro a hx; simp only [exists_prop, mem_map, mem_comap] at hx
  rcases hx with ⟨y, hy, hy'⟩
  rw [← mul_inv_cancel_left y a]
  exact mul_mem_sup hy (by simp [mem_ker, hy'])

lemma map_comap_eq_self {f : LatticeHom α β} {L : Sublattice β} (h : L ≤ f.range) : map f (comap f L) = L := by rwa [map_comap_eq, inf_eq_right]

lemma map_comap_eq_self_of_surjective {f : LatticeHom α β} (h : Surjective f) (L : Sublattice β) :
    map f (comap f L) = L :=
  map_comap_eq_self ((range_top_of_surjective _ h).symm ▸ le_top)

lemma comap_le_comap_of_le_range {f : LatticeHom α β} {L L : Sublattice β} (hf : L ≤ f.range) :
    L.comap f ≤ L.comap f ↔ L ≤ L :=
  ⟨(map_comap_eq_self hf).ge.trans ∘ map_le_iff_le_comap.mpr, comap_mono⟩

lemma comap_le_comap_of_surjective {f : LatticeHom α β} {L L : Sublattice β} (hf : Surjective f) :
    L.comap f ≤ L.comap f ↔ L ≤ L :=
  comap_le_comap_of_le_range (le_top.trans (f.range_top_of_surjective hf).ge)

lemma comap_lt_comap_of_surjective {f : LatticeHom α β} {L L : Sublattice β} (hf : Surjective f) :
    L.comap f < L.comap f ↔ L < L := by simp_rw [lt_iff_le_not_le, comap_le_comap_of_surjective hf]

lemma comap_injective {f : LatticeHom α β} (h : Surjective f) : Injective (comap f) :=
  fun L L ↦ by simp only [le_antisymm_iff, comap_le_comap_of_surjective h, imp_self]

lemma comap_map_eq_self {f : LatticeHom α β} (h : f.ker ≤ L) : comap f (map f L) = L := by rwa [comap_map_eq, sup_eq_left]

lemma comap_map_eq_self_of_injective {f : LatticeHom α β} (h : Injective f) (L : Sublattice α) :
    comap f (map f L) = L :=
  comap_map_eq_self (((ker_eq_bot_iff _).mpr h).symm ▸ bot_le)

lemma map_le_map_iff {f : LatticeHom α β} {L M : Sublattice α} : L.map f ≤ L.map f ↔ L ≤ L ⊔ f.ker := by
  rw [map_le_iff_le_comap, comap_map_eq]

lemma map_le_map_iff' {f : LatticeHom α β} {L M : Sublattice α} :
    L.map f ≤ L.map f ↔ L ⊔ f.ker ≤ L ⊔ f.ker := by
  simp only [map_le_map_iff, sup_le_iff, le_sup_right, and_true_iff]

lemma map_eq_map_iff {f : LatticeHom α β} {L M : Sublattice α} :
    L.map f = L.map f ↔ L ⊔ f.ker = L ⊔ f.ker := by simp only [le_antisymm_iff, map_le_map_iff']

lemma map_eq_range_iff {f : LatticeHom α β} : L.map f = f.range ↔ Codisjoint L f.ker := by rw [f.range_eq_map, map_eq_map_iff, codisjoint_iff, top_sup_eq]

lemma map_le_map_iff_of_injective {f : LatticeHom α β} (hf : Injective f) {L M : Sublattice α} :
    L.map f ≤ L.map f ↔ L ≤ L := by rw [map_le_iff_le_comap, comap_map_eq_self_of_injective hf]

lemma map_subtype_le_map_subtype {G' : Sublattice α} {L L : Sublattice G'} :
    L.map G'.subtype ≤ L.map G'.subtype ↔ L ≤ L :=
  map_le_map_iff_of_injective $ by apply Subtype.coe_injective

lemma map_injective {f : LatticeHom α β} (h : Injective f) : Injective (map f) :=
  LeftInverse.injective $ comap_map_eq_self_of_injective h

lemma map_eq_comap_of_inverse {f : LatticeHom α β} {g : β →* α} (hl : LeftInverse g f)
    (hr : RightInverse g f) (L : Sublattice α) : map f L = comap g L :=
  SetLike.ext' $ by rw [coe_map, coe_comap, Set.image_eq_preimage_of_inverse hl hr]

/-- Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`. -/
lemma map_injective_of_ker_le {L M : Sublattice α} (hH : f.ker ≤ L) (hK : f.ker ≤ L)
    (hf : map f L = map f L) : L = L := by
  apply_fun comap f at hf
  rwa [comap_map_eq, comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf

lemma closure_preimage_eq_top (s : Set α) : closure ((closure s).subtype ⁻¹' s) = ⊤ := by
  apply map_injective (closure s).subtype_injective
  rw [LatticeHom.map_closure, ← LatticeHom.range_eq_map, subtype_range,
    Set.image_preimage_eq_of_subset]
  rw [coeSubtype, Subtype.range_coe_subtype]
  exact subset_closure

lemma comap_sup_eq_of_le_range {L L : Sublattice β} (hH : L ≤ f.range) (hK : L ≤ f.range) :
    comap f L ⊔ comap f L = comap f (L ⊔ L) :=
  map_injective_of_ker_le f ((ker_le_comap f L).trans le_sup_left) (ker_le_comap f (L ⊔ L))
    (by
      rw [map_comap_eq, map_sup, map_comap_eq, map_comap_eq, inf_eq_right.mpr hH,
        inf_eq_right.mpr hK, inf_eq_right.mpr (sup_le hH hK)])

lemma comap_sup_eq (L L : Sublattice β) (hf : Surjective f) :
    comap f L ⊔ comap f L = comap f (L ⊔ L) :=
  comap_sup_eq_of_le_range f (le_top.trans (ge_of_eq (f.range_top_of_surjective hf)))
    (le_top.trans (ge_of_eq (f.range_top_of_surjective hf)))

lemma sup_SublatticeOf_eq {L L M : Sublattice α} (hH : L ≤ L) (hK : L ≤ L) :
    L.SublatticeOf L ⊔ L.SublatticeOf L = (L ⊔ L).SublatticeOf L :=
  comap_sup_eq_of_le_range L.subtype (hH.trans L.subtype_range.ge) (hK.trans L.subtype_range.ge)

lemma codisjoint_SublatticeOf_sup (L M : Sublattice α) :
    Codisjoint (L.SublatticeOf (L ⊔ L)) (L.SublatticeOf (L ⊔ L)) := by
  rw [codisjoint_iff, sup_SublatticeOf_eq, SublatticeOf_self]
  exacts [le_sup_left, le_sup_right]

/-- A sublattice is isomorphic to its image under an injective  If you have an isomorphism,
use `MulEquiv.SublatticeMap` for better definitional equalities. -/
noncomputable def equivMapOfInjective (L : Sublattice α) (f : LatticeHom α β) (hf : Injective f) :
    L ≃o L.map f :=
  { Equiv.Set.image f L hf with map_mul' := fun _ _ ↦ Subtype.ext (f.map_mul _ _) }

lemma coe_equivMapOfInjective_apply (L : Sublattice α) (f : LatticeHom α β) (hf : Injective f)
    (h : L) : (equivMapOfInjective L f hf h : β) = f h :=
  rfl

end Sublattice

namespace LatticeHom

variable {G₁ G₂ G₃ : Type*} [Lattice G₁] [Lattice G₂] [Lattice G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
def liftOfRightInverseAux (hf : RightInverse f_inv f) (g : G₁ →* G₃) (hg : f.ker ≤ g.ker) :
    G₂ →* G₃ where
  toFun b := g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro a y
    rw [← g.map_mul, ← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
    apply hg
    rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one, f.map_mul]
    simp only [hf _]

lemma liftOfRightInverseAux_comp_apply (hf : RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (a : G₁) : (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a := by
  dsimp [liftOfRightInverseAux]
  rw [← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
  apply hg
  rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one]
  simp only [hf _]

/-- `liftOfRightInverse f hf g hg` is the unique lattice homomorphism `φ`

* such that `φ.comp f = g` (`LatticeHom.liftOfRightInverse_comp`),
* where `f : G₁ →+* G₂` has a RightInverse `f_inv` (`hf`),
* and `g : G₂ →+* G₃` satisfies `hg : f.ker ≤ g.ker`.

See `LatticeHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   G₁.
   |  \
 f |   \ g
   |    \
   v     \⌟
   G₂----> G₃
      ∃!φ
```
 -/
      "`liftOfRightInverse f f_inv hf g hg` is the unique additive lattice homomorphism `φ`
      * such that `φ.comp f = g` (`AddLatticeHom.liftOfRightInverse_comp`),
      * where `f : G₁ →+ G₂` has a RightInverse `f_inv` (`hf`),
      * and `g : G₂ →+ G₃` satisfies `hg : f.ker ≤ g.ker`.
      See `AddLatticeHom.eq_liftOfRightInverse` for the uniqueness lemma.
      ```
         G₁.
         |  \\
       f |   \\ g
         |    \\
         v     \\⌟
         G₂----> G₃
            ∃!φ
      ```"]
def liftOfRightInverse (hf : RightInverse f_inv f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃)
    where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun a hx ↦ (mem_ker _).mpr $ by simp [(mem_ker _).mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply, Subtype.coe_mk]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `LatticeHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `surjInv`. -/
      "A non-computable version of `AddLatticeHom.liftOfRightInverse` for when no
      computable right inverse is available."]
noncomputable abbrev liftOfSurjective (hf : Surjective f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃) :=
  f.liftOfRightInverse (surjInv hf) (rightInverse_surjInv hf)

lemma liftOfRightInverse_comp_apply (hf : RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) (a : G₁) :
    (f.liftOfRightInverse f_inv hf g) (f a) = g.1 a :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 a

lemma liftOfRightInverse_comp (hf : RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) : (f.liftOfRightInverse f_inv hf g).comp f = g :=
  LatticeHom.ext $ f.liftOfRightInverse_comp_apply f_inv hf g

lemma eq_liftOfRightInverse (hf : RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (h : G₂ →* G₃) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end LatticeHom

variable {β : Type*} [Lattice β]

namespace LatticeHom

/-- The `LatticeHom` from the preimage of a sublattice to itself. -/
def SublatticeComap (f : α →* G') (H' : Sublattice G') : H'.comap f →* H' :=
  f.submonoidComap H'.toSubmonoid

/-- The `LatticeHom` from a sublattice to its image. -/
def SublatticeMap (f : α →* G') (L : Sublattice α) : L →* L.map f :=
  f.submonoidMap L.toSubmonoid

lemma sublatticeMap_surjective (f : α →* G') (L : Sublattice α) :
    Surjective (f.SublatticeMap L) :=
  f.submonoidMap_surjective L.toSubmonoid

end LatticeHom

namespace MulEquiv

variable {L M : Sublattice α}

/-- Makes the identity isomorphism from a proof two sublattices of a multiplicative
    lattice are equal. -/
def SublatticeCongr (h : L = L) : L ≃o L :=
  { Equiv.setCongr $ congr_arg _ h with map_mul' := fun _ _ ↦ rfl }

/-- A sublattice is isomorphic to its image under an isomorphism. If you only have an injective map,
use `Sublattice.equiv_map_of_injective`. -/
def SublatticeMap (e : α ≃o G') (L : Sublattice α) : L ≃o L.map (e : α →* G') :=
  MulEquiv.submonoidMap (e : α ≃o G') L.toSubmonoid

lemma coe_SublatticeMap_apply (e : α ≃o G') (L : Sublattice α) (g : L) :
    ((SublatticeMap e L g : L.map (e : α →* G')) : G') = e g :=
  rfl

lemma sublatticeMap_symm_apply (e : α ≃o G') (L : Sublattice α) (g : L.map (e : α →* G')) :
    (e.SublatticeMap L).symm g = ⟨e.symm g, SetLike.mem_coe.1 $ Set.mem_image_equiv.1 g.2⟩ :=
  rfl

end MulEquiv

namespace Sublattice

lemma equivMapOfInjective_coe_mulEquiv (L : Sublattice α) (e : α ≃o G') :
    L.equivMapOfInjective (e : α →* G') (EquivLike.injective e) = e.SublatticeMap L := by
  ext
  rfl

variable {C : Type*} [CommGroup C] {s t : Sublattice C} {a : C}

lemma mem_sup : a ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = a :=
  ⟨fun h ↦ by
    rw [← closure_eq s, ← closure_eq t, ← closure_union] at h
    refine Sublattice.closure_induction h ?_ ?_ ?_ ?_
    · rintro y (h | h)
      · exact ⟨y, h, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, y, h, by simp⟩
    · exact ⟨1, s.one_mem, 1, ⟨t.one_mem, mul_one 1⟩⟩
    · rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨_, mul_mem hy₁ hy₂, _, mul_mem hz₁ hz₂, by simp [mul_assoc, mul_left_comm]⟩
    · rintro _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨_, inv_mem hy, _, inv_mem hz, mul_comm z y ▸ (mul_inv_rev z y).symm⟩, by
    rintro ⟨y, hy, z, hz, rfl⟩; exact mul_mem_sup hy hz⟩

lemma mem_sup' : a ∈ s ⊔ t ↔ ∃ (y : s) (z : t), (y : C) * z = a :=
  mem_sup.trans $ by simp only [SetLike.exists, coe_mk, exists_prop]

lemma mem_closure_pair {a y z : C} :
    z ∈ closure ({a, y} : Set C) ↔ ∃ m n : ℤ, a ^ m * y ^ n = z := by
  rw [← Set.singleton_union, Sublattice.closure_union, mem_sup]
  simp_rw [mem_closure_singleton, exists_exists_eq_and]

instance : IsModularLattice (Sublattice C) :=
  ⟨fun {a} y z xz a ha ↦ by
    rw [mem_inf, mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

end Sublattice
