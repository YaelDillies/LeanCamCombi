/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Marked groups

This file defines group markings and induces a norm on marked groups.

## Main declarations

* `GroupMarking G S`: Marking of the group `G` by a type `S`, namely a surjective monoid
  homomorphism `FreeGroup S →* G`.
* `MarkedGroup`: If `m : GroupMarking G S`, then `MarkedGroup m` is a type synonym for `G`
  endowed with the metric coming from `m`.
* `MarkedGroup.instNormedGroup`: A marked group is normed by its marking.

## TODO

Protect `List.le_antisymm`
-/

open Function List Nat

variable {G S : Type*} [Group G]

/-- A marking of an additive group is a generating family of elements. -/
structure AddGroupMarking (G S : Type*) [AddGroup G] extends FreeAddGroup S →+ G where
  toFun_surjective : Surjective toFun

/-- A marking of a group is a generating family of elements. -/
@[to_additive]
structure GroupMarking (G S : Type*) [Group G] extends FreeGroup S →* G where
  toFun_surjective : Surjective toFun

/-- Reinterpret a marking of `G` by `S` as an additive monoid homomorphism `free_add_group S →+ G`.
-/
add_decl_doc AddGroupMarking.toAddMonoidHom

/-- Reinterpret a marking of `G` by `S` as a monoid homomorphism `FreeGroup S →+ G`. -/
add_decl_doc GroupMarking.toMonoidHom

namespace GroupMarking

@[to_additive]
instance instFunLike : FunLike (GroupMarking G S) (FreeGroup S) G where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨_, _⟩, _⟩, _⟩; congr!

@[to_additive]
instance instMonoidHomClass : MonoidHomClass (GroupMarking G S) (FreeGroup S) G where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[to_additive]
lemma coe_surjective (m : GroupMarking G S) : Surjective m := m.toFun_surjective

end GroupMarking

/-- The trivial group marking. -/
@[to_additive "The trivial additive group marking."]
def GroupMarking.refl : GroupMarking G G :=
  { FreeGroup.lift id with toFun_surjective := fun x => ⟨FreeGroup.of x, FreeGroup.lift.of⟩ }

@[to_additive] instance : Inhabited (GroupMarking G G) := ⟨.refl⟩

variable {m : GroupMarking G S}

set_option linter.unusedVariables false in
/-- A type synonym of `G`, tagged with a group marking. -/
@[to_additive "A type synonym of `G`, tagged with an additive group marking."]
def MarkedGroup (m : GroupMarking G S) : Type _ := G

@[to_additive] instance MarkedGroup.instGroup : Group (MarkedGroup m) := ‹Group G›

/-- "Identity" isomorphism between `G` and a group marking of it. -/
@[to_additive "\"Identity\" isomorphism between `G` and an additive group marking of it."]
def toMarkedGroup : G ≃* MarkedGroup m := .refl _

/-- "Identity" isomorphism between a group marking of `G` and itself. -/
@[to_additive "\"Identity\" isomorphism between an additive group marking of `G` and itself."]
def ofMarkedGroup : MarkedGroup m ≃* G := .refl _

@[to_additive (attr := simp)]
lemma toMarkedGroup_symm_eq : (toMarkedGroup : G ≃* MarkedGroup m).symm = ofMarkedGroup := rfl

@[to_additive (attr := simp)]
lemma ofMarkedGroup_symm_eq : (ofMarkedGroup : MarkedGroup m ≃* G).symm = toMarkedGroup := rfl

@[to_additive (attr := simp)]
lemma toMarkedGroup_ofMarkedGroup (a) : toMarkedGroup (ofMarkedGroup (a : MarkedGroup m)) = a := rfl

@[to_additive (attr := simp)]
lemma ofMarkedGroup_toMarkedGroup (a) : ofMarkedGroup (toMarkedGroup a : MarkedGroup m) = a := rfl

@[to_additive (attr := simp)]
lemma toMarkedGroup_inj {a b} : (toMarkedGroup a : MarkedGroup m) = toMarkedGroup b ↔ a = b := .rfl

@[to_additive (attr := simp)]
lemma ofMarkedGroup_inj {a b : MarkedGroup m} : ofMarkedGroup a = ofMarkedGroup b ↔ a = b := .rfl

variable (α : Type*)

@[to_additive]
instance MarkedGroup.instInhabited [Inhabited G] : Inhabited (MarkedGroup m) := ‹Inhabited G›

@[to_additive]
instance MarkedGroup.instSmul [SMul G α] : SMul (MarkedGroup m) α := ‹SMul G α›

@[to_additive]
instance MarkedGroup.instMulAction [MulAction G α] : MulAction (MarkedGroup m) α := ‹MulAction G α›

@[to_additive (attr := simp)]
lemma toMarkedGroup_smul (g : G) (x : α) [SMul G α] :
    (toMarkedGroup g : MarkedGroup m) • x = g • x := rfl

@[to_additive (attr := simp)]
lemma ofMarkedGroup_smul (g : MarkedGroup m) (x : α) [SMul G α] : ofMarkedGroup g • x = g • x := rfl

@[to_additive]
private lemma mul_aux [DecidableEq S] (x : MarkedGroup m) :
    ∃ (n : _) (l : FreeGroup S), toMarkedGroup (m l) = x ∧ l.toWord.length ≤ n := by
  classical
  obtain ⟨l, rfl⟩ := m.coe_surjective x
  exact ⟨_, _, rfl, le_rfl⟩

@[to_additive]
private lemma mul_aux' [DecidableEq S] (x : MarkedGroup m) :
    ∃ (n : _) (l : FreeGroup S), toMarkedGroup (m l) = x ∧ l.toWord.length = n := by
  classical
  obtain ⟨l, rfl⟩ := m.coe_surjective x
  exact ⟨_, _, rfl, rfl⟩

@[to_additive]
private lemma find_mul_aux [DecidableEq S] (x : MarkedGroup m)
    [DecidablePred fun n ↦ ∃ l, toMarkedGroup (m l) = x ∧ l.toWord.length ≤ n]
    [DecidablePred fun n ↦ ∃ l, toMarkedGroup (m l) = x ∧ l.toWord.length = n] :
    Nat.find (mul_aux x) = Nat.find (mul_aux' x) := by
  classical
  exact _root_.le_antisymm (Nat.find_mono fun n => Exists.imp fun l => And.imp_right le_of_eq) <|
    (Nat.le_find_iff _ _).2 fun k hk ⟨l, hl, hlk⟩ => (Nat.lt_find_iff _ _).1 hk _ hlk ⟨l, hl, rfl⟩

@[to_additive]
noncomputable instance : NormedGroup (MarkedGroup m) :=
  GroupNorm.toNormedGroup
    { toFun := fun x => by classical exact (Nat.find (mul_aux x)).cast
      map_one' := by
        classical
        exact cast_eq_zero.2 <| (find_eq_zero <| mul_aux _).2 ⟨1, by simp_rw [map_one], le_rfl⟩
      mul_le' := fun x y => by
        classical
        dsimp
        norm_cast
        obtain ⟨a, rfl, ha⟩ := Nat.find_spec (mul_aux x)
        obtain ⟨b, rfl, hb⟩ := Nat.find_spec (mul_aux y)
        refine find_le ⟨a * b, by simp, (a.toWord_mul_sublist _).length_le.trans ?_⟩
        rw [length_append]
        gcongr
      inv' := by
        classical
        suffices ∀ {x : MarkedGroup m}, Nat.find (mul_aux x⁻¹) ≤ Nat.find (mul_aux x) by
          dsimp
          refine fun _ => congr_arg Nat.cast (this.antisymm ?_)
          convert this
          simp_rw [inv_inv]
        rintro x
        refine find_mono fun nI => ?_
        rintro ⟨l, hl, h⟩
        exact ⟨l⁻¹, by simp [hl], h.trans_eq' <| by simp⟩
      eq_one_of_map_eq_zero' := fun x hx => by
        classical
        obtain ⟨l, rfl, hl⟩ := (find_eq_zero <| mul_aux _).1 (cast_eq_zero.1 hx)
        rw [le_zero_iff, length_eq_zero, ← FreeGroup.toWord_one] at hl
        rw [FreeGroup.toWord_injective hl, map_one, map_one] }

@[to_additive]
instance : DiscreteTopology (MarkedGroup (GroupMarking.refl : GroupMarking G G)) :=
  sorry

namespace MarkedGroup

@[to_additive]
lemma norm_def [DecidableEq S] (x : MarkedGroup m)
    [DecidablePred fun n ↦ ∃ l, toMarkedGroup (m l) = x ∧ l.toWord.length = n] :
    ‖x‖ = Nat.find (mul_aux' x) := by
  convert congr_arg Nat.cast (find_mul_aux _)
  classical
  infer_instance

@[to_additive (attr := simp)]
lemma norm_eq_one (x : MarkedGroup m) :
    ‖x‖ = 1 ↔ ∃ s, toMarkedGroup (m <| FreeGroup.mk [s]) = x := by
  classical
  simp_rw [norm_def, Nat.cast_eq_one, Nat.find_eq_iff, length_eq_one]
  constructor
  · rintro ⟨⟨l, rfl, s, hl⟩, hn⟩
    refine ⟨s, ?_⟩
    rw [← hl, FreeGroup.mk_toWord]
  rintro ⟨s, rfl⟩
  refine ⟨⟨_, rfl, s, ?_⟩, ?_⟩
  simp only [FreeGroup.toWord_mk, FreeGroup.reduce_singleton]
  sorry

@[simp]
lemma norm_toMarkedGroup (s : S) : ‖(toMarkedGroup (m (FreeGroup.of s)) : MarkedGroup m)‖ = 1 :=
  sorry

lemma gen_set_mul_right (x : MarkedGroup m) (s : S) :
    ‖(toMarkedGroup (ofMarkedGroup x * m (FreeGroup.of s)) : MarkedGroup m)‖ ≤ ‖x‖ + 1 :=
  sorry

lemma gen_set_mul_right' (x : MarkedGroup m) {n : ℝ} (hx : ‖x‖ ≤ n) (s : S) :
    ‖(toMarkedGroup (ofMarkedGroup x * m (FreeGroup.of s)) : MarkedGroup m)‖ ≤ n + 1 :=
  sorry

lemma gen_set_mul_left (x : MarkedGroup m) (s : S) :
    ‖(toMarkedGroup (m (FreeGroup.of s) * ofMarkedGroup x) : MarkedGroup m)‖ ≤ ‖x‖ + 1 :=
  sorry

lemma gen_set_mul_left' (x : MarkedGroup m) {n : ℝ} (hx : ‖x‖ ≤ n) (s : S) :
    ‖(toMarkedGroup (m (FreeGroup.of s) * ofMarkedGroup x) : MarkedGroup m)‖ ≤ n + 1 :=
  sorry

lemma dist_one_iff (x y : MarkedGroup m) :
    dist x y = 1 ↔ (∃ s : S, x * toMarkedGroup (m (.of s)) = y) ∨
      ∃ s : S, y * toMarkedGroup (m (.of s)) = x :=
  sorry

lemma gen_set_div (x : MarkedGroup m) (hx : x ≠ 1) :
    ∃ y : MarkedGroup m, dist x y = 1 ∧ ‖y‖ = ‖x‖ - 1 :=
  sorry

lemma gen_div_left (x : MarkedGroup m) (hx : x ≠ 1) :
    ∃ y : MarkedGroup m,
      ((∃ s : S, toMarkedGroup (m (.of s)) * y = x) ∨
        ∃ s : S, toMarkedGroup (m (.of s)⁻¹) * y = x) ∧ ‖y‖ = ‖x‖ - 1 :=
  sorry

-- same lemmas but for subsets
lemma gen_norm_le_one_sub {H : Set G} {m' : GroupMarking G H} {s : MarkedGroup m'} (sh : s ∈ H) :
    ‖s‖ ≤ 1 :=
  sorry

lemma gen_set_mul_right_sub {H : Set G} {s : G} {m' : GroupMarking G H} (sh : s ∈ H)
    (g : MarkedGroup m') : ‖g * toMarkedGroup s‖ ≤ ‖g‖ + 1 :=
  sorry

lemma gen_set_mul_right'_sub {H : Set G} {s : G} {m' : GroupMarking G H} (sh : s ∈ H)
    (g : MarkedGroup m') {n : ℝ} (hg : ‖g‖ ≤ n) : ‖g * toMarkedGroup s‖ ≤ n + 1 :=
  sorry

lemma gen_set_mul_left_sub {H : Set G} {m' : GroupMarking G H} (g s : MarkedGroup m')
    (sh : s ∈ H) : ‖s * g‖ ≤ ‖g‖ + 1 :=
  sorry

lemma gen_set_mul_left'_sub {H : Set G} {m' : GroupMarking G H} (g s : MarkedGroup m')
    (sh : s ∈ H) {n : ℝ} (hg : ‖g‖ ≤ n) : ‖s * g‖ ≤ n + 1 :=
  sorry

lemma dist_one_iff_sub {H : Set G} {m' : GroupMarking G H} (x y : MarkedGroup m') :
    dist x y = 1 ↔ (∃ s ∈ H, x * toMarkedGroup s = y) ∨ ∃ s ∈ H, y * toMarkedGroup s = x :=
  sorry

lemma gen_div_left_sub {H : Set G} {m' : GroupMarking G H} (x : MarkedGroup m') (hx : x ≠ 1) :
    ∃ y : MarkedGroup m', ((∃ s ∈ H, toMarkedGroup s * y = x) ∨
      ∃ s ∈ H, (toMarkedGroup s)⁻¹ * y = x) ∧ ‖y‖ = ‖x‖ - 1 :=
  sorry

end MarkedGroup
