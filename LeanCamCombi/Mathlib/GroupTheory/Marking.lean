/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.GroupTheory.FreeGroup

/-!
# Marked groups

This file defines group markings and induces a norm on marked groups.

## Main declarations

* `group_marking G S`: Marking of the group `G` by a type `S`, namely a surjective monoid
  homomorphism `free_group S →* G`.
* `marked_group`: If `m : group_marking G S`, then `marked_group m` is a type synonym for `G`
  endowed with the metric coming from `m`.
* `marked_group.normed_group`: A marked group is normed by its marking.
-/


namespace FreeGroup

variable {α : Type _} [DecidableEq α]

@[simp, to_additive]
theorem reduce_nil : reduce ([] : List (α × Bool)) = [] :=
  rfl

@[to_additive]
theorem reduce_singleton (s : α × Bool) : reduce [s] = [s] :=
  rfl

end FreeGroup

open Function List Nat

variable {G S : Type _} [Group G]

/-- A marking of an additive group is a generating family of elements. -/
structure AddGroupMarking (G S : Type _) [AddGroup G] extends FreeAddGroup S →+ G where
  toFun_surjective : Surjective to_fun

/-- A marking of a group is a generating family of elements. -/
@[to_additive]
structure GroupMarking (G S : Type _) [Group G] extends FreeGroup S →* G where
  toFun_surjective : Surjective to_fun

/-- Reinterpret a marking of `G` by `S` as an additive monoid homomorphism `free_add_group S →+ G`.
-/
add_decl_doc AddGroupMarking.toAddMonoidHom

/-- Reinterpret a marking of `G` by `S` as a monoid homomorphism `free_group S →+ G`. -/
add_decl_doc GroupMarking.toMonoidHom

namespace GroupMarking

@[to_additive]
instance : MonoidHomClass (GroupMarking G S) (FreeGroup S) G
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_hMul f := f.map_mul'
  map_one f := f.map_one'

@[to_additive]
theorem coe_surjective (m : GroupMarking G S) : Surjective m :=
  m.toFun_surjective

end GroupMarking

/-- The trivial group marking. -/
@[to_additive "The trivial additive group marking."]
def GroupMarking.refl : GroupMarking G G :=
  { FreeGroup.lift id with toFun_surjective := fun x => ⟨FreeGroup.of x, FreeGroup.lift.of⟩ }

@[to_additive]
instance : Inhabited (GroupMarking G G) :=
  ⟨GroupMarking.refl⟩

variable {G S} {m : GroupMarking G S}

/-- A type synonym of `G`, tagged with a group marking. -/
@[nolint unused_arguments,
  to_additive "A type synonym of `G`, tagged with an additive group marking."]
def MarkedGroup (m : GroupMarking G S) : Type _ :=
  G
deriving Group

attribute [to_additive] MarkedGroup.group

/-- "Identity" isomorphism between `G` and a group marking of it. -/
@[to_additive "\"Identity\" isomorphism between `G` and an additive group marking of it."]
def toMarkedGroup : G ≃* MarkedGroup m :=
  MulEquiv.refl _

/-- "Identity" isomorphism between a group marking of `G` and itself. -/
@[to_additive "\"Identity\" isomorphism between an additive group marking of `G` and itself."]
def ofMarkedGroup : MarkedGroup m ≃* G :=
  MulEquiv.refl _

@[simp, to_additive]
theorem toMarkedGroup_symm_eq : (toMarkedGroup : G ≃* MarkedGroup m).symm = ofMarkedGroup :=
  rfl

@[simp, to_additive]
theorem ofMarkedGroup_symm_eq : (ofMarkedGroup : MarkedGroup m ≃* G).symm = toMarkedGroup :=
  rfl

@[simp, to_additive]
theorem toMarkedGroup_ofMarkedGroup (a) : toMarkedGroup (ofMarkedGroup (a : MarkedGroup m)) = a :=
  rfl

@[simp, to_additive]
theorem ofMarkedGroup_toMarkedGroup (a) : ofMarkedGroup (toMarkedGroup a : MarkedGroup m) = a :=
  rfl

@[simp, to_additive]
theorem toMarkedGroup_inj {a b} : (toMarkedGroup a : MarkedGroup m) = toMarkedGroup b ↔ a = b :=
  Iff.rfl

@[simp, to_additive]
theorem ofMarkedGroup_inj {a b : MarkedGroup m} : ofMarkedGroup a = ofMarkedGroup b ↔ a = b :=
  Iff.rfl

variable (α : Type _)

@[to_additive]
instance [Inhabited G] : Inhabited (MarkedGroup m) :=
  ‹Inhabited G›

@[to_additive]
instance MarkedGroup.hasSmul [SMul G α] : SMul (MarkedGroup m) α :=
  ‹SMul G α›

@[to_additive]
instance MarkedGroup.mulAction [MulAction G α] : MulAction (MarkedGroup m) α :=
  ‹MulAction G α›

@[simp, to_additive]
theorem toMarkedGroup_smul (g : G) (x : α) [SMul G α] :
    (toMarkedGroup g : MarkedGroup m) • x = g • x :=
  rfl

@[simp, to_additive]
theorem ofMarkedGroup_smul (g : MarkedGroup m) (x : α) [SMul G α] : ofMarkedGroup g • x = g • x :=
  rfl

@[to_additive]
private theorem mul_aux [DecidableEq S] (x : MarkedGroup m) :
    ∃ (n : _) (l : FreeGroup S), toMarkedGroup (m l) = x ∧ l.toWord.length ≤ n := by
  classical
  obtain ⟨l, rfl⟩ := m.coe_surjective x
  exact ⟨_, _, rfl, le_rfl⟩

@[to_additive]
private theorem mul_aux' [DecidableEq S] (x : MarkedGroup m) :
    ∃ (n : _) (l : FreeGroup S), toMarkedGroup (m l) = x ∧ l.toWord.length = n := by
  classical
  obtain ⟨l, rfl⟩ := m.coe_surjective x
  exact ⟨_, _, rfl, rfl⟩

@[to_additive]
theorem find_mul_aux [DecidableEq S] (x : MarkedGroup m) : by
    classical exact Nat.find (mul_aux x) = Nat.find (mul_aux' x) :=
  le_antisymm (Nat.find_mono fun n => Exists.imp fun l => And.imp_right le_of_eq) <|
    (Nat.le_find_iff _ _).2 fun k hk ⟨l, hl, hlk⟩ => (Nat.lt_find_iff _ _).1 hk _ hlk ⟨l, hl, rfl⟩

@[to_additive]
noncomputable instance : NormedGroup (MarkedGroup m) :=
  GroupNorm.toNormedGroup
    { toFun := fun x => by classical exact Nat.find (mul_aux x)
      map_one' := cast_eq_zero.2 <| (find_eq_zero <| mul_aux _).2 ⟨1, by simp_rw [map_one], le_rfl⟩
      hMul_le' := fun x y => by
        norm_cast
        obtain ⟨a, rfl, ha⟩ := Nat.find_spec (mul_aux x)
        obtain ⟨b, rfl, hb⟩ := Nat.find_spec (mul_aux y)
        refine' find_le ⟨a * b, map_mul _ _ _, (a.to_word_mul_sublist _).length_le.trans _⟩
        rw [length_append]
        exact add_le_add ha hb
      inv' := by
        suffices ∀ {x : MarkedGroup m}, Nat.find (mul_aux x⁻¹) ≤ Nat.find (mul_aux x) by
          refine' fun _ => congr_arg coe (this.antisymm _)
          convert this
          simp_rw [inv_inv]
        refine' fun x => find_mono fun nI => _
        rintro ⟨l, hl, h⟩
        exact ⟨l⁻¹, by simp [hl], h.trans_eq' <| by simp⟩
      eq_one_of_map_eq_zero' := fun x hx => by
        obtain ⟨l, rfl, hl⟩ := (find_eq_zero <| mul_aux _).1 (cast_eq_zero.1 hx)
        rw [le_zero_iff, length_eq_zero, ← FreeGroup.toWord_one] at hl
        rw [FreeGroup.toWord_injective hl, map_one, map_one] }

@[to_additive]
instance : DiscreteTopology (MarkedGroup (GroupMarking.refl : GroupMarking G G)) :=
  sorry

namespace MarkedGroup

@[to_additive]
theorem norm_def (x : MarkedGroup m) : ‖x‖ = Nat.find (mul_aux' x) :=
  congr_arg coe (find_mul_aux _)

@[simp, to_additive]
theorem norm_eq_one (x : MarkedGroup m) :
    ‖x‖ = 1 ↔ ∃ s, toMarkedGroup (m <| FreeGroup.mk [s]) = x := by
  simp_rw [norm_def, Nat.cast_eq_one, Nat.find_eq_iff, length_eq_one]
  constructor
  · rintro ⟨⟨l, rfl, s, hl⟩, hn⟩
    refine' ⟨s, _⟩
    rw [← hl, FreeGroup.mk_toWord]
  rintro ⟨s, rfl⟩
  refine' ⟨⟨_, rfl, s, _⟩, _⟩
  simp only [FreeGroup.toWord_mk, FreeGroup.reduce_singleton]
  sorry
  sorry

@[simp]
theorem norm_toMarkedGroup (s : S) : ‖(toMarkedGroup (m (FreeGroup.of s)) : MarkedGroup m)‖ = 1 :=
  sorry

theorem gen_set_hMul_right (x : MarkedGroup m) (s : S) :
    ‖(toMarkedGroup (ofMarkedGroup x * m (FreeGroup.of s)) : MarkedGroup m)‖ ≤ ‖x‖ + 1 :=
  sorry

theorem gen_set_hMul_right' (x : MarkedGroup m) {n : ℝ} (hx : ‖x‖ ≤ n) (s : S) :
    ‖(toMarkedGroup (ofMarkedGroup x * m (FreeGroup.of s)) : MarkedGroup m)‖ ≤ n + 1 :=
  sorry

theorem gen_set_hMul_left (x : MarkedGroup m) (s : S) :
    ‖(toMarkedGroup (m (FreeGroup.of s) * ofMarkedGroup x) : MarkedGroup m)‖ ≤ ‖x‖ + 1 :=
  sorry

theorem gen_set_hMul_left' (x : MarkedGroup m) {n : ℝ} (hx : ‖x‖ ≤ n) (s : S) :
    ‖(toMarkedGroup (m (FreeGroup.of s) * ofMarkedGroup x) : MarkedGroup m)‖ ≤ n + 1 :=
  sorry

theorem dist_one_iff (x y : MarkedGroup m) :
    dist x y = 1 ↔ (∃ s : S, x * m (FreeGroup.of s) = y) ∨ ∃ s : S, y * m (FreeGroup.of s) = x :=
  sorry

theorem gen_set_div (x : MarkedGroup m) (hx : x ≠ 1) :
    ∃ y : MarkedGroup m, dist x y = 1 ∧ ‖y‖ = ‖x‖ - 1 :=
  sorry

theorem gen_div_left (x : MarkedGroup m) (hx : x ≠ 1) :
    ∃ y : MarkedGroup m,
      ((∃ s : S, m (FreeGroup.of s) * y = x) ∨ ∃ s : S, m (FreeGroup.of s)⁻¹ * y = x) ∧
        ‖y‖ = ‖x‖ - 1 :=
  sorry

-- same lemmas but for subsets
theorem gen_norm_le_one_sub {H : Set G} {m' : GroupMarking G H} {s : MarkedGroup m'} (sh : s ∈ H) :
    ‖s‖ ≤ 1 :=
  sorry

theorem gen_set_hMul_right_sub {H : Set G} {s : G} {m' : GroupMarking G H} (sh : s ∈ H)
    (g : MarkedGroup m') : ‖g * s‖ ≤ ‖g‖ + 1 :=
  sorry

theorem gen_set_hMul_right'_sub {H : Set G} {s : G} {m' : GroupMarking G H} (sh : s ∈ H)
    (g : MarkedGroup m') {n : ℝ} (hg : ‖g‖ ≤ n) : ‖g * s‖ ≤ n + 1 :=
  sorry

theorem gen_set_hMul_left_sub {H : Set G} {m' : GroupMarking G H} (g s : MarkedGroup m')
    (sh : s ∈ H) : ‖s * g‖ ≤ ‖g‖ + 1 :=
  sorry

theorem gen_set_hMul_left'_sub {H : Set G} {m' : GroupMarking G H} (g s : MarkedGroup m')
    (sh : s ∈ H) {n : ℝ} (hg : ‖g‖ ≤ n) : ‖s * g‖ ≤ n + 1 :=
  sorry

theorem dist_one_iff_sub {H : Set G} {m' : GroupMarking G H} (x y : MarkedGroup m') :
    dist x y = 1 ↔ (∃ s ∈ H, x * s = y) ∨ ∃ s ∈ H, y * s = x :=
  sorry

theorem gen_div_left_sub {H : Set G} {m' : GroupMarking G H} (x : MarkedGroup m') (hx : x ≠ 1) :
    ∃ y : MarkedGroup m', ((∃ s ∈ H, s * y = x) ∨ ∃ s ∈ H, s⁻¹ * y = x) ∧ ‖y‖ = ‖x‖ - 1 :=
  sorry

end MarkedGroup
