import Mathlib.Data.Finset.Sups

/-!
# Set family operations

This file defines a few binary operations on `Finset α` for use in set family combinatorics.

## Main declarations

* `s \\ t`: Finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
* `Finset.disjDiffs s t`: Finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t` and `a`
  and `b` are disjoint.

## Notation

We define the following notation in locale `FinsetFamily`:
* `s \\ t`
* `s\^c ` for `Finset.disjDiffs s t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

-- TODO: Is there a better spot for those two instances?
namespace Finset
variable {α : Type*} [Preorder α] {s t : Set α} {a : α}

instance decidablePredMemUpperClosure (s : Finset α) [@DecidableRel α (· ≤ ·)] :
    DecidablePred (· ∈ upperClosure (s : Set α)) := fun _ => decidableExistsAndFinset
#align finset.decidable_pred_mem_upper_closure Finset.decidablePredMemUpperClosure

instance decidablePredMemLowerClosure (s : Finset α) [@DecidableRel α (· ≤ ·)] :
    DecidablePred (· ∈ lowerClosure (s : Set α)) := fun _ => decidableExistsAndFinset
#align finset.decidable_pred_mem_lower_closure Finset.decidablePredMemLowerClosure

end Finset

open Function
open scoped FinsetFamily

variable {α : Type*} [DecidableEq α]

namespace Finset
section SemilatticeSup
variable [SemilatticeSup α] [@DecidableRel α (· ≤ ·)]

lemma filter_sups_le (s t : Finset α) (a : α) :
    (s ⊻ t).filter (· ≤ a) = s.filter (· ≤ a) ⊻ t.filter (· ≤ a) := by
  ext b
  simp only [mem_filter, mem_sups]
  constructor
  · rintro ⟨⟨b, hb, c, hc, rfl⟩, ha⟩
    rw [sup_le_iff] at ha
    exact ⟨_, ⟨hb, ha.1⟩, _, ⟨hc, ha.2⟩, rfl⟩
  · rintro ⟨b, hb, c, hc, _, rfl⟩
    exact ⟨⟨_, hb.1, _, hc.1, rfl⟩, _root_.sup_le hb.2 hc.2⟩

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [@DecidableRel α (· ≤ ·)]

lemma filter_infs_ge (s t : Finset α) (a : α) :
    (s ⊼ t).filter (a ≤ ·) = s.filter (a ≤ ·) ⊼ t.filter (a ≤ ·) := by
  ext b
  simp only [mem_filter, mem_infs]
  constructor
  · rintro ⟨⟨b, hb, c, hc, rfl⟩, ha⟩
    rw [le_inf_iff] at ha
    exact ⟨_, ⟨hb, ha.1⟩, _, ⟨hc, ha.2⟩, rfl⟩
  · rintro ⟨b, hb, c, hc, _, rfl⟩
    exact ⟨⟨_, hb.1, _, hc.1, rfl⟩, _root_.le_inf hb.2 hc.2⟩

end SemilatticeInf
end Finset

namespace Finset
section Diffs
variable [GeneralizedBooleanAlgebra α] (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s \\ t` is the finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`. -/
def diffs : Finset α → Finset α → Finset α := image₂ (· \ ·)

scoped[FinsetFamily] infixl:74 " \\\\ " => Finset.diffs
  -- This notation is meant to have higher precedence than `\` and `⊓`, but still within the
  -- realm of other binary notation

open FinsetFamily

variable {s t} {a b c : α}

@[simp] lemma mem_diffs : c ∈ s \\ t ↔ ∃ a ∈ s, ∃ b ∈ t, a \ b = c := by simp [(· \\ ·)]

variable (s t)

@[simp, norm_cast] lemma coe_diffs : (↑(s \\ t) : Set α) = Set.image2 (· \ ·) s t :=
  coe_image₂ _ _ _

lemma card_diffs_le : (s \\ t).card ≤ s.card * t.card := card_image₂_le _ _ _

lemma card_diffs_iff :
    (s \\ t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun x ↦ x.1 \ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}

lemma sdiff_mem_diffs : a ∈ s → b ∈ t → a \ b ∈ s \\ t := mem_image₂_of_mem

lemma diffs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ \\ t₁ ⊆ s₂ \\ t₂ := image₂_subset
lemma diffs_subset_left : t₁ ⊆ t₂ → s \\ t₁ ⊆ s \\ t₂ := image₂_subset_left
lemma diffs_subset_right : s₁ ⊆ s₂ → s₁ \\ t ⊆ s₂ \\ t := image₂_subset_right

lemma image_subset_diffs_left : b ∈ t → (s.image fun a ↦ a \ b) ⊆ s \\ t :=
  image_subset_image₂_left

lemma image_subset_diffs_right : a ∈ s → t.image (a \ ·) ⊆ s \\ t :=
  image_subset_image₂_right (f := (· \ ·))

lemma forall_diffs_iff {p : α → Prop} : (∀ c ∈ s \\ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a \ b) :=
  forall_image₂_iff

@[simp] lemma diffs_subset_iff : s \\ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a \ b ∈ u := image₂_subset_iff

@[simp] lemma diffs_nonempty : (s \\ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

protected lemma Nonempty.diffs : s.Nonempty → t.Nonempty → (s \\ t).Nonempty := Nonempty.image₂

lemma Nonempty.of_diffs_left : (s \\ t).Nonempty → s.Nonempty := Nonempty.of_image₂_left
lemma Nonempty.of_diffs_right : (s \\ t).Nonempty → t.Nonempty := Nonempty.of_image₂_right

@[simp] lemma empty_diffs : ∅ \\ t = ∅ := image₂_empty_left
@[simp] lemma diffs_empty : s \\ ∅ = ∅ := image₂_empty_right
@[simp] lemma diffs_eq_empty : s \\ t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[simp] lemma singleton_diffs : {a} \\ t = t.image fun b ↦ a \ b := image₂_singleton_left
@[simp] lemma diffs_singleton : s \\ {b} = s.image fun a ↦ a \ b := image₂_singleton_right
lemma singleton_diffs_singleton : ({a} \\ {b} : Finset α) = {a \ b} := image₂_singleton

lemma diffs_union_left : (s₁ ∪ s₂) \\ t = s₁ \\ t ∪ s₂ \\ t := image₂_union_left
lemma diffs_union_right : s \\ (t₁ ∪ t₂) = s \\ t₁ ∪ s \\ t₂ := image₂_union_right

lemma diffs_inter_subset_left : (s₁ ∩ s₂) \\ t ⊆ s₁ \\ t ∩ s₂ \\ t := image₂_inter_subset_left
lemma diffs_inter_subset_right : s \\ (t₁ ∩ t₂) ⊆ s \\ t₁ ∩ s \\ t₂ := image₂_inter_subset_right

lemma subset_diffs {s t : Set α} :
    ↑u ⊆ Set.image2 (· \ ·) s t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' \\ t' :=
  subset_image₂

variable (s t u)

lemma biUnion_image_sdiff_left : s.biUnion (fun a ↦ t.image $ (· \ ·) a) = s \\ t :=
  biUnion_image_left

lemma biUnion_image_sdiff_right : t.biUnion (fun b ↦ s.image fun a ↦ a \ b) = s \\ t :=
  biUnion_image_right

lemma image_sdiff_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· \ ·)) = s \\ t :=
  image_uncurry_product _ _ _

lemma diffs_right_comm : s \\ t \\ u = s \\ u \\ t := image₂_right_comm sdiff_right_comm

end Diffs

section Compls
variable [BooleanAlgebra α] (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s` is the finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
def compls : Finset α → Finset α := map ⟨compl, compl_injective⟩

scoped[FinsetFamily] postfix:max "ᶜˢ"   => Finset.compls

open FinsetFamily

variable {s t} {a b c : α}

@[simp] lemma mem_compls : a ∈ sᶜˢ ↔ aᶜ ∈ s := by
  rw [Iff.comm, ←mem_map' ⟨compl, compl_injective⟩, Embedding.coeFn_mk, compl_compl, compls]

variable (s t)

@[simp] lemma image_compl : s.image compl = sᶜˢ := by simp [compls, map_eq_image]

@[simp, norm_cast] lemma coe_compls : (↑sᶜˢ : Set α) = compl '' ↑s := coe_map _ _

@[simp] lemma card_compls : sᶜˢ.card = s.card := card_map _

variable {s s₁ s₂ t t₁ t₂ u}

lemma compl_mem_compls : a ∈ s → aᶜ ∈ sᶜˢ := mem_map_of_mem _
@[simp] lemma compls_subset_compls : s₁ᶜˢ ⊆ s₂ᶜˢ ↔ s₁ ⊆ s₂ := map_subset_map
lemma forall_compls_iff {p : α → Prop} : (∀ a ∈ sᶜˢ, p a) ↔ ∀ a ∈ s, p aᶜ := forall_mem_map
lemma exists_compls_iff {p : α → Prop} : (∃ a ∈ sᶜˢ, p a) ↔ ∃ a ∈ s, p aᶜ := by aesop

@[simp] lemma compls_compls (s : Finset α) : sᶜˢᶜˢ = s := by ext; simp

lemma compls_subset_iff : sᶜˢ ⊆ t ↔ s ⊆ tᶜˢ := by rw [←compls_subset_compls, compls_compls]

@[simp] lemma compls_nonempty : sᶜˢ.Nonempty ↔ s.Nonempty := map_nonempty

protected alias ⟨Nonempty.of_compls, Nonempty.compls⟩ := compls_nonempty

@[simp] lemma compls_empty : (∅ : Finset α)ᶜˢ = ∅ := map_empty _
@[simp] lemma compls_eq_empty : sᶜˢ = ∅ ↔ s = ∅ := map_eq_empty
@[simp] lemma compls_singleton (a : α) : {a}ᶜˢ = {aᶜ} := map_singleton _ _
@[simp] lemma compls_univ [Fintype α] : (univ : Finset α)ᶜˢ = univ := by ext; simp
@[simp] lemma compls_union (s t : Finset α) : (s ∪ t)ᶜˢ = sᶜˢ ∪ tᶜˢ := map_union _ _
@[simp] lemma compls_inter (s t : Finset α) : (s ∩ t)ᶜˢ = sᶜˢ ∩ tᶜˢ := map_inter _ _

@[simp] lemma compls_infs (s t : Finset α) : (s ⊼ t)ᶜˢ = sᶜˢ ⊻ tᶜˢ := by
  simp_rw [←image_compl]; exact image_image₂_distrib λ _ _ ↦ compl_inf

@[simp] lemma compls_sups (s t : Finset α) : (s ⊻ t)ᶜˢ = sᶜˢ ⊼ tᶜˢ := by
  simp_rw [←image_compl]; exact image_image₂_distrib λ _ _ ↦ compl_sup

@[simp] lemma infs_compls_eq_diffs (s t : Finset α) : s ⊼ tᶜˢ = s \\ t := by
  ext; simp [sdiff_eq]; aesop

@[simp] lemma compls_infs_eq_diffs (s t : Finset α) : sᶜˢ ⊼ t = t \\ s := by
  rw [infs_comm, infs_compls_eq_diffs]

@[simp] lemma diffs_compls_eq_infs (s t : Finset α) : s \\ tᶜˢ = s ⊼ t := by
  rw [←infs_compls_eq_diffs, compls_compls]

end Compls
end Finset
