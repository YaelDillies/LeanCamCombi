import Mathlib.Order.Lattice
import LeanCamCombi.Mathlib.Data.Set.Prod
import LeanCamCombi.Mathlib.Logic.Nontrivial.Basic
import LeanCamCombi.Mathlib.Order.Hom.Lattice
import LeanCamCombi.Mathlib.Order.SupClosed

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

variable {ι : Sort*} (α β γ : Type*) [Lattice α] [Lattice β] [Lattice γ]

/-- A sublattice of a lattice is a set containing the suprema and infima of any of its elements. -/
structure Sublattice where
  /-- The underlying set of a sublattice. **Do not use directly**. Instead, use the coercion
  `Sublattice α → Set α`, which Lean should automatically insert for you in most cases. -/
  carrier : Set α
  supClosed' : SupClosed carrier
  infClosed' : InfClosed carrier

variable {α β γ}

namespace Sublattice
variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a : α}

initialize_simps_projections Sublattice (carrier → coe)

instance instSetLike : SetLike (Sublattice α) α where
  coe L := L.carrier
  coe_injective' L M h := by cases L; congr

lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq

@[simp] lemma supClosed (L : Sublattice α) : SupClosed (L : Set α) := L.supClosed'
@[simp] lemma infClosed (L : Sublattice α) : InfClosed (L : Set α) := L.infClosed'
@[simp] lemma latticeClosed (L : Sublattice α) : LatticeClosed (L : Set α) :=
  ⟨L.supClosed', L.infClosed'⟩

@[simp] lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := Iff.rfl
@[simp] lemma mem_mk (h_sup h_inf) : a ∈ mk s h_sup h_inf ↔ a ∈ s := Iff.rfl
@[simp, norm_cast] lemma coe_mk (h_sup h_inf) : mk s h_sup h_inf = s := rfl
@[simp] lemma mk_le_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf ≤ mk t ht_sup ht_inf ↔ s ⊆ t := Iff.rfl
@[simp] lemma mk_lt_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf < mk t ht_sup ht_inf ↔ s ⊂ t := Iff.rfl

/-- Copy of a sublattice with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (L : Sublattice α) (s : Set α) (hs : s = L) : Sublattice α where
  carrier := s
  supClosed' := hs.symm ▸ L.supClosed'
  infClosed' := hs.symm ▸ L.infClosed'

@[simp, norm_cast] lemma coe_copy (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = s := rfl

lemma copy_eq (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = L := SetLike.coe_injective hs

/-- Two sublattices are equal if they have the same elements. -/
lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext

/-- A sublattice of a lattice inherits a supremum. -/
instance instSupCoe : Sup L where
  sup a b := ⟨a ⊔ b, L.supClosed a.2 b.2⟩

/-- A sublattice of a lattice inherits an infimum. -/
instance instInfCoe : Inf L where
  inf a b := ⟨a ⊓ b, L.infClosed a.2 b.2⟩

@[simp, norm_cast] lemma coe_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
@[simp, norm_cast] lemma coe_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
@[simp] lemma mk_sup_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩ :=
  rfl
@[simp] lemma mk_inf_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩ :=
  rfl

/-- A sublattice of a lattice inherits a lattice structure. -/
instance instLatticeCoe (L : Sublattice α) : Lattice L :=
  Subtype.coe_injective.lattice _ (λ _ _ ↦ rfl) (λ _ _ ↦ rfl)

/-- A sublattice of a distributive lattice inherits a distributive lattice structure. -/
instance instDistribLatticeCoe {α : Type*} [DistribLattice α] (L : Sublattice α) :
    DistribLattice L :=
  Subtype.coe_injective.distribLattice _ (λ _ _ ↦ rfl) (λ _ _ ↦ rfl)

/-- The natural lattice hom from a sublattice to the original lattice. -/
def subtype (L : Sublattice α) : LatticeHom L α where
  toFun := ((↑) : L → α)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp, norm_cast] lemma coe_subtype (L : Sublattice α) : L.subtype = ((↑) : L → α) := rfl
lemma subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a := rfl

lemma subtype_injective (L : Sublattice α) : Injective $ subtype L := Subtype.coe_injective

/-- The inclusion homomorphism from a sublattice `L` to a bigger sublattice `M`. -/
def inclusion (h : L ≤ M) : LatticeHom L M where
  toFun := Set.inclusion h
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp] lemma coe_inclusion (h : L ≤ M) : inclusion h = Set.inclusion h := rfl
lemma inclusion_apply (h : L ≤ M) (a : L) : inclusion h a = Set.inclusion h a := rfl

lemma inclusion_injective (h : L ≤ M) : Injective $ inclusion h := Set.inclusion_injective h

@[simp] lemma inclusion_rfl (L : Sublattice α) : inclusion le_rfl = LatticeHom.id L := rfl
@[simp] lemma subtype_comp_inclusion (h : L ≤ M) : M.subtype.comp (inclusion h) = L.subtype := rfl

/-- The maximum sublattice of a lattice. -/
instance instTop : Top (Sublattice α) where
  top.carrier := univ
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

/-- The empty sublattice of a lattice. -/
instance instBot : Bot (Sublattice α) where
  bot.carrier := ∅
  bot.supClosed' := supClosed_empty
  bot.infClosed' := infClosed_empty

/-- The inf of two sublattices is their intersection. -/
instance instInf : Inf (Sublattice α) where
  inf L M := { carrier := L ∩ M
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

/-- The inf of sublattices is their intersection. -/
instance instInfSet : InfSet (Sublattice α) where
  sInf S := { carrier := ⨅ L ∈ S, L
              supClosed' := supClosed_sInter $ forall_range_iff.2 $ λ L ↦ supClosed_sInter $
                forall_range_iff.2 λ _ ↦ L.supClosed
              infClosed' := infClosed_sInter $ forall_range_iff.2 $ λ L ↦ infClosed_sInter $
                forall_range_iff.2 λ _ ↦ L.infClosed }

instance instInhabited : Inhabited (Sublattice α) := ⟨⊥⟩

/-- The top sublattice is isomorphic to the lattice.

This is the sublattice version of `Equiv.Set.univ α`. -/
def topEquiv : (⊤ : Sublattice α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := Iff.rfl

@[simp, norm_cast] lemma coe_top : (⊤ : Sublattice α) = (univ : Set α) := rfl
@[simp, norm_cast] lemma coe_bot : (⊥ : Sublattice α) = (∅ : Set α) := rfl
@[simp, norm_cast] lemma coe_inf' (L M : Sublattice α) : L ⊓ M = (L : Set α) ∩ M := rfl
@[simp, norm_cast] lemma coe_sInf (S : Set (Sublattice α)) : sInf S = ⋂ L ∈ S, (L : Set α) := rfl
@[simp, norm_cast] lemma coe_iInf (f : ι → Sublattice α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by
  simp [iInf]

@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by rw [←coe_top, coe_inj]
@[simp, norm_cast] lemma coe_eq_empty : L = (∅ : Set α) ↔ L = ⊥ := by rw [←coe_bot, coe_inj]

@[simp] lemma not_mem_bot (a : α) : a ∉ (⊥ : Sublattice α) := id
@[simp] lemma mem_top (a : α) : a ∈ (⊤ : Sublattice α) := mem_univ _
@[simp] lemma mem_inf : a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M := Iff.rfl
@[simp] lemma mem_sInf {S : Set (Sublattice α)} : a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L := by
  rw [←SetLike.mem_coe]; simp
@[simp] lemma mem_iInf {f : ι → Sublattice α} : a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
  rw [←SetLike.mem_coe]; simp

/-- Sublattices of a lattice form a complete lattice. -/
instance instCompleteLattice : CompleteLattice (Sublattice α) :=
  { completeLatticeOfInf (Sublattice α)
      λ _s ↦ IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := λ _S _a ↦ False.elim
    top := ⊤
    le_top := λ _S a _ha ↦ mem_top a
    inf := (· ⊓ ·)
    le_inf := λ _L _M _N hM hN _a ha ↦ ⟨hM ha, hN ha⟩
    inf_le_left := λ _L _M _a ↦ And.left
    inf_le_right := λ _L _M _a ↦ And.right }

lemma subsingleton_iff : Subsingleton (Sublattice α) ↔ IsEmpty α :=
  ⟨λ _ ↦ univ_eq_empty_iff.1 $ coe_inj.2 $ Subsingleton.elim ⊤ ⊥,
    λ _ ↦ SetLike.coe_injective.subsingleton⟩

lemma nontrivial_iff : Nontrivial (Sublattice α) ↔ Nonempty α := by
  rw [←not_subsingleton_iff_nontrivial, subsingleton_iff, not_isEmpty_iff]

instance [IsEmpty α] : Unique (Sublattice α) where
  uniq _ := @Subsingleton.elim _ (subsingleton_iff.2 ‹_›) _ _

instance [Nonempty α] : Nontrivial (Sublattice α) := nontrivial_iff.2 ‹_›

/-- The preimage of a sublattice along a lattice homomorphism. -/
def comap (f : LatticeHom α β) (L : Sublattice β) : Sublattice α where
  carrier := f ⁻¹' L
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

@[simp, norm_cast] lemma coe_comap (L : Sublattice β) (f : LatticeHom α β) : L.comap f = f ⁻¹' L :=
  rfl

@[simp] lemma mem_comap {L : Sublattice β} : a ∈ L.comap f ↔ f a ∈ L := Iff.rfl

lemma comap_mono : Monotone (comap f) := λ _ _ ↦ preimage_mono

@[simp] lemma comap_id (L : Sublattice α) : L.comap (LatticeHom.id _) = L := rfl

@[simp] lemma comap_comap (L : Sublattice γ) (g : LatticeHom β γ) (f : LatticeHom α β) :
    (L.comap g).comap f = L.comap (g.comp f) := rfl

/-- The image of a sublattice along a monoid homomorphism is a sublattice. -/
def map (f : LatticeHom α β) (L : Sublattice α) : Sublattice β where
  carrier := f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f

@[simp] lemma coe_map (f : LatticeHom α β) (L : Sublattice α) : (L.map f : Set β) = f '' L := rfl
@[simp] lemma mem_map {b : β} : b ∈ L.map f ↔ ∃ a ∈ L, f a = b := Iff.rfl

lemma mem_map_of_mem (f : LatticeHom α β) {a : α} : a ∈ L → f a ∈ L.map f := mem_image_of_mem f
lemma apply_coe_mem_map (f : LatticeHom α β) (a : L) : f a ∈ L.map f := mem_map_of_mem f a.prop

lemma map_mono : Monotone (map f) := λ _ _ ↦ image_subset _

@[simp] lemma map_id : L.map (LatticeHom.id α) = L := SetLike.coe_injective $ image_id _

@[simp] lemma map_map (g : LatticeHom β γ) (f : LatticeHom α β) :
    (L.map f).map g = L.map (g.comp f) := SetLike.coe_injective $ image_image _ _ _

lemma mem_map_equiv {f : α ≃o β} {a : β} : a ∈ L.map f ↔ f.symm a ∈ L := Set.mem_image_equiv

lemma apply_mem_map_iff (hf : Injective f) : f a ∈ L.map f ↔ a ∈ L := hf.mem_set_image

lemma map_equiv_eq_comap_symm (f : α ≃o β) (L : Sublattice α) :
    L.map f = L.comap (f.symm : LatticeHom β α) :=
  SetLike.coe_injective $ f.toEquiv.image_eq_preimage L

lemma comap_equiv_eq_map_symm (f : β ≃o α) (L : Sublattice α) :
    L.comap f = L.map (f.symm : LatticeHom α β) := (map_equiv_eq_comap_symm f.symm L).symm

lemma map_symm_eq_iff_eq_map {M : Sublattice β} {e : β ≃o α} :
    L.map ↑e.symm = M ↔ L = M.map ↑e := by
  simp_rw [←coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

lemma map_le_iff_le_comap {f : LatticeHom α β} {M : Sublattice β} : L.map f ≤ M ↔ L ≤ M.comap f :=
  image_subset_iff

lemma gc_map_comap (f : LatticeHom α β) : GaloisConnection (map f) (comap f) :=
  λ _ _ ↦ map_le_iff_le_comap

@[simp] lemma map_bot (f : LatticeHom α β) : (⊥ : Sublattice α).map f = ⊥ := (gc_map_comap f).l_bot

lemma map_sup (f : LatticeHom α β) (L M : Sublattice α) : (L ⊔ M).map f = L.map f ⊔ M.map f :=
  (gc_map_comap f).l_sup

lemma map_iSup (f : LatticeHom α β) (L : ι → Sublattice α) : (⨆ i, L i).map f = ⨆ i, (L i).map f :=
  (gc_map_comap f).l_iSup

@[simp] lemma comap_top (f : LatticeHom α β) : (⊤ : Sublattice β).comap f = ⊤ :=
  (gc_map_comap f).u_top

lemma comap_inf (L M : Sublattice β) (f : LatticeHom α β) :
    (L ⊓ M).comap f = L.comap f ⊓ M.comap f := (gc_map_comap f).u_inf

lemma comap_iInf (f : LatticeHom α β) (s : ι → Sublattice β) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (gc_map_comap f).u_iInf

lemma map_inf_le (L M : Sublattice α) (f : LatticeHom α β) : map f (L ⊓ M) ≤ map f L ⊓ map f M :=
  map_mono.map_inf_le _ _

lemma le_comap_sup (L M : Sublattice β) (f : LatticeHom α β) :
    comap f L ⊔ comap f M ≤ comap f (L ⊔ M) := comap_mono.le_map_sup _ _

lemma le_comap_iSup (f : LatticeHom α β) (L : ι → Sublattice β) :
    ⨆ i, (L i).comap f ≤ (⨆ i, L i).comap f := comap_mono.le_map_iSup

lemma map_inf (L M : Sublattice α) (f : LatticeHom α β) (hf : Injective f) :
    map f (L ⊓ M) = map f L ⊓ map f M := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

lemma map_top (f : LatticeHom α β) (h : Surjective f) : Sublattice.map f ⊤ = ⊤ :=
  SetLike.coe_injective $ by simp [h.range_eq]

/-- The product of two sublattices as a sublattice. -/
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
  ext λ a ↦ by simp [mem_prod, LatticeHom.coe_fst]

lemma top_prod (L : Sublattice β) : (⊤ : Sublattice α).prod L = L.comap (LatticeHom.snd α β) :=
  ext λ a ↦ by simp [mem_prod, LatticeHom.coe_snd]

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

/-- A version of `Set.pi` for Sublattices. Given an index set `s` and a family of submodules
`s : Π i, Sublattice f i`, `pi s s` is the Sublattice of dependent functions `f : Π i, f i` such that
`f i` belongs to `pi s s` whenever `i ∈ s`. -/
def pi (s : Set κ) (L : ∀ i, Sublattice (π i)) : Sublattice (∀ i, π i) where
  carrier := s.pi λ i ↦ L i
  supClosed' := supClosed_pi λ i _ ↦ (L i).supClosed
  infClosed' := infClosed_pi λ i _ ↦ (L i).infClosed

@[simp, norm_cast] lemma coe_pi (s : Set κ) (L : ∀ i, Sublattice (π i)) :
    (pi s L : Set (∀ i, π i)) = Set.pi s λ i ↦ L i := rfl

@[simp] lemma mem_pi {s : Set κ} {L : ∀ i, Sublattice (π i)} {x : ∀ i, π i} :
    x ∈ pi s L ↔ ∀ i, i ∈ s → x i ∈ L i := Iff.rfl

@[simp] lemma pi_empty (L : ∀ i, Sublattice (π i)) : pi ∅ L = ⊤ := ext λ a ↦ by simp [mem_pi]

@[simp] lemma pi_top (s : Set κ) : (pi s λ i ↦ ⊤ : Sublattice (∀ i, π i)) = ⊤ :=
  ext λ a ↦ by simp [mem_pi]

@[simp] lemma pi_bot [Nonempty κ] : (pi univ λ i ↦ ⊥ : Sublattice (∀ i, π i)) = ⊥ :=
  ext λ a ↦ by simp [mem_pi]

lemma le_pi {s : Set κ} {L : ∀ i, Sublattice (π i)} {M : Sublattice (∀ i, π i)} :
    M ≤ pi s L ↔ ∀ i ∈ s, M ≤ comap (Pi.evalLatticeHom π i) (L i) := by simp [SetLike.le_def]; aesop

@[simp] lemma pi_univ_eq_bot {L : ∀ i, Sublattice (π i)} : pi univ L = ⊥ ↔ ∃ i, L i = ⊥ := by
  simp_rw [←coe_inj]; simp

end Pi
end Sublattice

open Sublattice

namespace LatticeHom
variable {β : Type*} {P : Type*} [Lattice β] [Lattice P] (L : Sublattice α)

/-- Restriction of a lattice hom to a sublattice of the codomain. -/
def codRestrict (f : LatticeHom α β) (L : Sublattice β) (h : ∀ x, f x ∈ L) : LatticeHom α L where
  toFun := Set.codRestrict f L h
  map_sup' a b := Subtype.ext $ map_sup f a b
  map_inf' a b := Subtype.ext $ map_inf f a b

@[simp, norm_cast] lemma coe_codRestrict (f : LatticeHom α β) (L : Sublattice β) (h) :
    codRestrict f L h = Set.codRestrict f L h := rfl

#exit

/-- The range of a monoid homomorphism from a lattice is a sublattice. -/
def range (f : LatticeHom α β) : Sublattice β :=
  Sublattice.copy ((⊤ : Sublattice α).map f) (Set.range f) (by simp [Set.ext_iff])

@[simp, norm_cast] lemma coe_range (f : LatticeHom α β) : (f.range : Set β) = Set.range f := rfl

@[simp] lemma mem_range {f : LatticeHom α β} {y : β} : y ∈ f.range ↔ ∃ a, f a = y :=
  Iff.rfl

@[simp] lemma map_top (f : LatticeHom α β) : (⊤ : Sublattice α).map f = f.range :=
  (Sublattice.copy_eq _ _ _).symm

lemma restrict_range (f : LatticeHom α β) : (f.restrict L).range = L.map f := by
  simp_rw [SetLike.ext_iff, mem_range, mem_map, restrict_apply, SetLike.exists,
    exists_prop, forall_const]

/-- The canonical surjective lattice homomorphism `α →* f(α)` induced by a lattice
homomorphism `LatticeHom α β`. -/
def rangeRestrict (f : LatticeHom α β) : LatticeHom α f.range :=
  codRestrict f _ λ a ↦ ⟨a, rfl⟩

lemma coe_rangeRestrict (f : LatticeHom α β) (g : α) : (f.rangeRestrict g : β) = f g :=
  rfl

lemma coe_comp_rangeRestrict (f : LatticeHom α β) :
    ((↑) : f.range → β) ∘ (⇑f.rangeRestrict : α → f.range) = f :=
  rfl

lemma subtype_comp_rangeRestrict (f : LatticeHom α β) : f.range.subtype.comp f.rangeRestrict = f :=
  ext $ f.coe_rangeRestrict

lemma rangeRestrict_surjective (f : LatticeHom α β) : Surjective f.rangeRestrict :=
  λ ⟨_, g, rfl⟩ ↦ ⟨g, rfl⟩

lemma rangeRestrict_injective_iff {f : LatticeHom α β} : Injective f.rangeRestrict ↔ Injective f := by
  convert Set.injective_codRestrict _

lemma map_range (g : β →* P) (f : LatticeHom α β) : f.range.map g = (g.comp f).range := by
  rw [range_eq_map, range_eq_map]; exact (⊤ : Sublattice α).map_map g f

lemma range_top_iff_surjective {β} [Lattice β] {f : LatticeHom α β} :
    f.range = (⊤ : Sublattice β) ↔ Surjective f :=
  SetLike.ext'_iff.trans $ Iff.trans (by rw [coe_range, coe_top]) Set.range_iff_surjective

/-- The range of a surjective monoid homomorphism is the whole of the codomain. -/
  "The range of a surjective `AddMonoid` homomorphism is the whole of the codomain."]
lemma range_top_of_surjective {β} [Lattice β] (f : LatticeHom α β) (hf : Surjective f) :
    f.range = (⊤ : Sublattice β) :=
  range_top_iff_surjective.2 hf

lemma range_one : (1 : LatticeHom α β).range = ⊥ :=
  SetLike.ext λ a ↦ by simpa using @comm _ (· = ·) _ 1 a

lemma _root_.Sublattice.subtype_range (L : Sublattice α) : L.subtype.range = L := by
  rw [range_eq_map, ← SetLike.coe_set_eq, coe_map, Sublattice.coeSubtype]
  ext
  simp

lemma _root_.Sublattice.inclusion_range {L M : Sublattice α} (h_le : L ≤ L) :
    (inclusion h_le).range = L.SublatticeOf L :=
  Sublattice.ext λ g ↦ Set.ext_iff.mp (Set.range_inclusion h_le) g

lemma sublatticeOf_range_eq_of_le {G₁ G₂ : Type*} [Lattice G₁] [Lattice G₂] {L : Sublattice G₂}
    (f : G₁ →* G₂) (h : f.range ≤ L) :
    f.range.SublatticeOf L = (f.codRestrict L λ a ↦ h ⟨a, rfl⟩).range := by
  ext k
  refine' exists_congr _
  simp [Subtype.ext_iff]

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
  MulEquiv.ofBijective (f.codRestrict f.range λ a ↦ ⟨a, rfl⟩)
    ⟨λ a y h ↦ hf (Subtype.ext_iff.mp h), by
      rintro ⟨a, y, rfl⟩
      exact ⟨y, rfl⟩⟩

lemma ofInjective_apply {f : LatticeHom α β} (hf : Injective f) {a : α} :
    ↑(ofInjective hf a) = f a :=
  rfl

lemma apply_ofInjective_symm {f : LatticeHom α β} (hf : Injective f) (a : f.range) :
    f ((ofInjective hf).symm a) = a :=
  Subtype.ext_iff.1 $ (ofInjective hf).apply_symm_apply a

section Ker

variable {M : Type*} [MulOneClass M]

/-- The multiplicative kernel of a monoid homomorphism is the Sublattice of elements `a : α` such that
`f a = 1` -/
def ker (f : α →* M) : Sublattice α :=
  { LatticeHom.mker f with
    inv_mem' := λ {a} (hx : f a = 1) ↦
      calc
        f x⁻¹ = f a * f x⁻¹ := by rw [hx, one_mul]
        _ = 1 := by rw [← map_mul, mul_inv_self, map_one] }

lemma mem_ker (f : α →* M) {a : α} : a ∈ f.ker ↔ f a = 1 :=
  Iff.rfl

lemma coe_ker (f : α →* M) : (f.ker : Set α) = (f : α → M) ⁻¹' {1} :=
  rfl

lemma ker_toHomUnits {M} [Monoid M] (f : α →* M) : f.toHomUnits.ker = f.ker := by
  ext a
  simp [mem_ker, Units.ext_iff]

lemma eq_iff (f : α →* M) {a y : α} : f a = f y ↔ y⁻¹ * a ∈ f.ker := by
  constructor <;> intro h
  · rw [mem_ker, map_mul, h, ← map_mul, inv_mul_self, map_one]
  · rw [← one_mul a, ← mul_inv_self y, mul_assoc, map_mul, f.mem_ker.1 h, mul_one]

instance decidableMemKer [DecidableEq M] (f : α →* M) : DecidablePred (· ∈ f.ker) := λ a ↦
  decidable_of_iff (f a = 1) f.mem_ker

lemma comap_ker (g : β →* P) (f : LatticeHom α β) : g.ker.comap f = (g.comp f).ker :=
  rfl

lemma comap_bot (f : LatticeHom α β) : (⊥ : Sublattice β).comap f = f.ker :=
  rfl

lemma ker_restrict (f : LatticeHom α β) : (f.restrict L).ker = f.ker.SublatticeOf L :=
  rfl

lemma ker_codRestrict {S} [SetLike S β] [SubmonoidClass S β] (f : LatticeHom α β) (s : S)
    (h : ∀ a, f a ∈ s) : (f.codRestrict s h).ker = f.ker :=
  SetLike.ext λ _x ↦ Subtype.ext_iff

lemma ker_rangeRestrict (f : LatticeHom α β) : ker (rangeRestrict f) = ker f :=
  ker_codRestrict _ _ _

lemma ker_one : (1 : α →* M).ker = ⊤ :=
  SetLike.ext λ _x ↦ eq_self_iff_true _

lemma ker_id : (LatticeHom.id α).ker = ⊥ :=
  rfl

lemma ker_eq_bot_iff (f : α →* M) : f.ker = ⊥ ↔ Injective f :=
  ⟨λ h a y hxy ↦ by rwa [eq_iff, h, mem_bot, inv_mul_eq_one, eq_comm] at hxy, λ h ↦
    bot_unique λ a hx ↦ h (hx.trans f.map_one.symm)⟩

lemma _root_.Sublattice.ker_subtype (L : Sublattice α) : L.subtype.ker = ⊥ :=
  L.subtype.ker_eq_bot_iff.mpr Subtype.coe_injective

lemma _root_.Sublattice.ker_inclusion {L M : Sublattice α} (h : L ≤ L) : (inclusion h).ker = ⊥ :=
  (inclusion h).ker_eq_bot_iff.mpr (Set.inclusion_injective h)

lemma prodMap_comap_prod {G' : Type*} {N' : Type*} [Lattice G'] [Lattice N'] (f : LatticeHom α β)
    (g : G' →* N') (S : Sublattice β) (S' : Sublattice N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective $ Set.preimage_prod_map_prod f g _ _

lemma ker_prodMap {G' : Type*} {N' : Type*} [Lattice G'] [Lattice N'] (f : LatticeHom α β) (g : G' →* N') :
    (prodMap f g).ker = f.ker.prod g.ker := by
  rw [← comap_bot, ← comap_bot, ← comap_bot, ← prodMap_comap_prod, bot_prod_bot]

lemma range_le_ker_iff (f : α →* G') (g : G' →* G'') : f.range ≤ g.ker ↔ g.comp f = 1 :=
  ⟨λ h ↦ ext λ a ↦ h ⟨a, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact FunLike.congr_fun h y⟩

instance (priority := 100) normal_ker (f : α →* M) : f.ker.Normal :=
  ⟨λ a hx y ↦ by
    rw [mem_ker, map_mul, map_mul, f.mem_ker.1 hx, mul_one, map_mul_eq_one f (mul_inv_self y)]⟩

lemma ker_fst : ker (fst α G') = .prod ⊥ ⊤ := SetLike.ext λ _ ↦ (and_true_iff _).symm

lemma ker_snd : ker (snd α G') = .prod ⊤ ⊥ := SetLike.ext λ _ ↦ (true_and_iff _).symm

end Ker

section EqLocus

variable {M : Type*} [Monoid M]

/-- The Sublattice of elements `a : α` such that `f a = g a` -/
def eqLocus (f g : α →* M) : Sublattice α :=
  { eqLocusM f g with inv_mem' := eq_on_inv f g }

lemma eqLocus_same (f : LatticeHom α β) : f.eqLocus f = ⊤ :=
  SetLike.ext λ _ ↦ eq_self_iff_true _

/-- If two monoid homomorphisms are equal on a set, then they are equal on its Sublattice closure. -/
      "If two monoid homomorphisms are equal on a set, then they are equal on its Sublattice
      closure."]
lemma eqOn_closure {f g : α →* M} {s : Set α} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from (closure_le _).2 h

lemma eq_of_eqOn_top {f g : α →* M} (h : Set.EqOn f g (⊤ : Sublattice α)) : f = g :=
  ext λ _x ↦ h trivial

lemma eq_of_eqOn_dense {s : Set α} (hs : closure s = ⊤) {f g : α →* M} (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_top $ hs ▸ eqOn_closure h

end EqLocus

lemma closure_preimage_le (f : LatticeHom α β) (s : Set β) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  (closure_le _).2 λ a hx ↦ by rw [SetLike.mem_coe, mem_comap]; exact subset_closure hx

/-- The image under a monoid homomorphism of the Sublattice generated by a set equals the Sublattice
generated by the image of the set. -/
lemma map_closure (f : LatticeHom α β) (s : Set α) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (Sublattice.gc_map_comap f) (Sublattice.gi β).gc
    (Sublattice.gi α).gc λ _t ↦ rfl

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

lemma map_comap_eq_self {f : LatticeHom α β} {L : Sublattice β} (h : L ≤ f.range) : map f (comap f L) = L :=
  by rwa [map_comap_eq, inf_eq_right]

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
  λ L L ↦ by simp only [le_antisymm_iff, comap_le_comap_of_surjective h, imp_self]

lemma comap_map_eq_self {f : LatticeHom α β} (h : f.ker ≤ L) : comap f (map f L) = L :=
  by rwa [comap_map_eq, sup_eq_left]

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

lemma map_eq_range_iff {f : LatticeHom α β} : L.map f = f.range ↔ Codisjoint L f.ker :=
  by rw [f.range_eq_map, map_eq_map_iff, codisjoint_iff, top_sup_eq]

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
  { Equiv.Set.image f L hf with map_mul' := λ _ _ ↦ Subtype.ext (f.map_mul _ _) }

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
  invFun φ := ⟨φ.comp f, λ a hx ↦ (mem_ker _).mpr $ by simp [(mem_ker _).mp hx]⟩
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
  { Equiv.setCongr $ congr_arg _ h with map_mul' := λ _ _ ↦ rfl }

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
  ⟨λ h ↦ by
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
  ⟨λ {a} y z xz a ha ↦ by
    rw [mem_inf, mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

end Sublattice

