/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import LeanCamCombi.Mathlib.Data.Set.Pointwise.SMul

/-!
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`. Further,
if the inequality is strict, then we in fact have `|s + H| + |t + H| ≤ |s + t|`.

## Main declarations

* `Finset.mul_kneser`: Kneser's theorem.
* `Finset.mul_strict_kneser`: Strict Kneser theorem.

## References

* [Imre Ruzsa, *Sumsets and structure*][ruzsa2009]
* Matt DeVos, *A short proof of Kneser's addition theorem*
-/

attribute [-simp] Set.singleton_mul Set.mul_singleton

set_option linter.haveLet 0

open Function MulAction MulOpposite
open scoped Classical Pointwise

variable {G : Type*} [CommGroup G]

local notation s " +ₛ " N => Finset.image ((↑) : G → G ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : G → G ⧸ N) s

local notation "Stab " s:arg => (MulAction.stabilizer G (s : Set G) : Set G)
@[to_additive bleh] abbrev coset (C s : Set G) (a : G) := s ∩ a • Stab C

open Lean PrettyPrinter Delaborator SubExpr

/-- Delaborator for `MulAction.stabilizer`. Pretty-print `MulAction.stabilizer α s` where
`s : Set α` or `s : Finset α` as `Stab s`. -/
@[delab app.MulAction.stabilizer]
def delabStab : Delab := whenPPOption getPPNotation do `(Stab $(← withNaryArg 4 <| delab))

namespace Set
variable {s s' t t' C : Set G} {a b : G}

@[to_additive]
lemma stabilizer_mul_subset_stabilizer (hs : (coset C s a).Nonempty)
    (ht : (coset C t b).Nonempty) :
    Stab (coset C s a * coset C t b) ⊆ Stab C := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := ht
  obtain ⟨c, hc, (hac : _ * _ = _)⟩ := hx.2
  obtain ⟨d, hd, (hbd : _ * _ = _)⟩ := hy.2
  rw [← smul_set_subset_smul_set_iff (a := (x * y))]
  calc
    (x * y) • Stab (coset C s a * coset C t b)
      ⊆ coset C s a * coset C t b := smul_set_stabilizer_subset <| mul_mem_mul hx hy
    _ ⊆ (a • Stab C) * (b • Stab C) := by gcongr <;> exact inter_subset_right
    _ = (a • c • Stab C) * (b • d • Stab C) := by rw [smul_coe_set hc, smul_coe_set hd]
    _ = (x * y) • Stab C := by
      rw [smul_smul, smul_smul, hac, hbd, smul_mul_smul_comm, coe_mul_coe]

@[to_additive]
lemma stabilizer_mul_ssubset_stabilizer (hs : (coset C s a).Nonempty)
    (ht : (coset C t b).Nonempty) (hab : ¬(a * b) • Stab C ⊆ s * t) :
    Stab (coset C s a * coset C t b) ⊂ Stab C := by
  obtain ⟨x, hx⟩ := id hs
  obtain ⟨y, hy⟩ := id ht
  obtain ⟨c, hc, hac⟩ := hx.2
  obtain ⟨d, hd, had⟩ := hy.2
  have : (a * b) • Stab C = (a * c * (b * d)) • Stab C := by
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc, ←
      mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_cancel (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_coe_set hc, smul_coe_set hd]
  have hsub : coset C s a * (coset C t b) ⊆ (a * b) • Stab C := by
    apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
    simp only [smul_mul_smul_comm, ← Subgroup.coe_mul, subset_refl]
    norm_cast
  have hxy : x * y ∈ coset C s a * (coset C t b) := mul_mem_mul hx hy
  rw [this] at hsub
  rw [this] at hab
  obtain ⟨z, hz, hzst⟩ := not_subset.1 hab
  obtain ⟨w, hw, rfl⟩ := hz
  refine (Set.ssubset_iff_of_subset <| stabilizer_mul_subset_stabilizer hs ht).mpr ⟨w, hw, ?_⟩
  rw [SetLike.mem_coe, mem_stabilizer_set]
  push_neg
  refine ⟨a * c * (b * d), .inr ⟨?_, by convert hxy⟩⟩
  rw [smul_eq_mul, mul_comm w, ← smul_eq_mul (a' := w)]
  exact fun h ↦ hzst <| mul_subset_mul inter_subset_left inter_subset_left h

@[to_additive]
lemma stabilizer_union_mul_subset_stabilizer (hC : C.Finite) (hab : ¬(a * b) • Stab C ⊆ s * t)
    (hCdisj : Disjoint (C : Set G) (coset C s a * coset C t b)) :
    Stab (C ∪ coset C s a * coset C t b) ⊆ Stab C := by
  rintro x hx
  rw [SetLike.mem_coe, mem_stabilizer_iff, smul_set_union] at hx
  suffices h : Disjoint (x • C) (coset C s a * coset C t b) by
    rw [SetLike.mem_coe, mem_stabilizer_set_iff_smul_set_subset hC]
    exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx)
  by_contra!
  rw [not_disjoint_iff_nonempty_inter] at this
  have hUn : ((⋃ y ∈ C, x • y • Stab C) ∩ (coset C s a * coset C t b)).Nonempty := by
    simpa [← smul_set_iUnion₂, iUnion_smul_set, ← stabilizer_coe_finset]
  simp_rw [iUnion_inter, nonempty_iUnion, ← smul_assoc, smul_eq_mul] at hUn
  obtain ⟨y, hy, hyne⟩ := hUn
  have hxyCsubC : (x * y) • Stab C ⊆ x • C := by
    rw [← smul_eq_mul, smul_assoc, smul_set_subset_smul_set_iff]
    exact smul_set_stabilizer_subset hy
  have hxyC : Disjoint ((x * y) • Stab C) (C * Stab C) :=
    isBlock_subgroup.disjoint_smul_set_smul fun hxyC ↦
      hyne.not_disjoint (hCdisj.mono_left $ le_iff_subset.2 (by simpa using hxyC))
  rw [mul_stabilizer_self] at hxyC
  have hxysub : (x * y) • Stab C ⊆ coset C s a * (coset C t b) :=
    hxyC.left_le_of_le_sup_left (hxyCsubC.trans $ subset_union_left.trans hx.subset')
  suffices coset C s a * (coset C t b) ⊂ (a * b) • Stab C by
    exact isBlock_subgroup.not_smul_set_ssubset_smul_set <| hxysub.trans_ssubset this
  apply ssubset_of_subset_not_subset
  · refine (mul_subset_mul inter_subset_right inter_subset_right).trans ?_
    simp only [smul_mul_smul_comm, coe_mul_coe, subset_refl]
  · contrapose! hab
    exact hab.trans (mul_subset_mul inter_subset_left inter_subset_left)

@[to_additive]
lemma stabilizer_union_mul_eq_stabilizer_mul (hC : C.Finite) (hab : ¬(a * b) • Stab C ⊆ s * t)
    (hs : (coset C s a : Set G).Nonempty) (ht : (↑t ∩ b • Stab C).Nonempty)
    (hCdisj : Disjoint (C : Set G) (coset C s a * coset C t b)) :
    Stab (C ∪ coset C s a * coset C t b) = Stab (coset C s a * coset C t b) := by
  congr! 1
  exact stabilizer_union_eq_right hCdisj (Set.stabilizer_mul_ssubset_stabilizer hs ht hab).subset <|
    stabilizer_union_mul_subset_stabilizer hC hab hCdisj

/-! ### Auxiliary results -/

local prefix:arg "#" => Set.ncard

@[to_additive]
lemma mul_aux1 (hCfin : C.Finite) (hs'fin : s'.Finite) (ht'fin : t'.Finite)
    (ih : #(↑s' * Stab (s' * t')) + #(t' * Stab (s' * t')) ≤ #(s' * t') + #(Stab (s' * t')))
    (hconv : #(s ∩ t) + #((s ∪ t) * Stab C) ≤ #C + #(Stab C))
    (hnotconv : #(C ∪ s' * t') + #(Stab (C ∪ s' * t')) < #(s ∩ t) + #((s ∪ t) * Stab (C ∪ s' * t')))
    (hCun : Stab (C ∪ s' * t') = Stab (s' * t')) (hdisj : Disjoint C (s' * t')) :
    (#((s ∪ t) * Stab C) - #((s ∪ t) * Stab (s' * t')) : ℤ) <
      #(Stab C) - #(s' * Stab (s' * t')) - #(t' * Stab (s' * t')) := by
  set H := Stab C
  set H' := Stab (s' * t')
  set C' := C ∪ s' * t'
  zify at hconv hnotconv ih
  calc
    (#((s ∪ t) * H) - #((s ∪ t) * H') : ℤ) < #C + #H - #(s ∩ t) - (#C' + #H' - #(s ∩ t)) := by
      rw [← hCun]
      linarith [hconv, hnotconv]
    _ = #H - #(s' * t') - #H' := by
      rw [ncard_union_eq hdisj hCfin (hs'fin.mul ht'fin), Int.ofNat_add]
      abel
    _ ≤ #H - #(s' * H') - #(t' * H') := by linarith [ih]

@[to_additive]
lemma disjoint_smul_stabilizer (hst : s ⊆ t) (has : ¬a • Stab s ⊆ t) : Disjoint s (a • Stab s) := by
  suffices Disjoint (s * Stab s) (a • Stab s) by simpa [stabilizer_mul_self]
  exact isBlock_subgroup.disjoint_smul_smul_set fun ha ↦ has <| ha.trans <| by simpa

@[to_additive]
lemma disjoint_mul_sub_card_le (b : G) (has : a ∈ s) (hCfin : C.Finite) (hsfin : s.Finite)
    (htfin : t.Finite) (hsC : Disjoint t (a • Stab C))
    (hst : Stab (coset C s a * coset C t b) ⊆ Stab C) :
    (#(Stab C) : ℤ) - #(coset C s a * Stab (coset C s a * coset C t b)) ≤
      #((s ∪ t) * Stab C) - #((s ∪ t) * Stab (coset C s a * coset C t b)) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp at hsC
    subst t
    have hs : s.Nonempty := ⟨a, has⟩
    simp [hs, coset]
  have hstabCfin : (Stab C : Set G).Finite := stabilizer_finite hC hCfin
  calc
    (#(Stab C) : ℤ) - #(coset C s a * Stab (coset C s a * coset C t b))
      = #(a • Stab C \ (coset C s a * Stab (coset C s a * coset C t b))) := by
      rw [cast_ncard_sdiff ((mul_subset_mul_left hst).trans <|
        (mul_subset_mul_right inter_subset_right).trans _) hstabCfin.smul_set,
        ncard_smul_set]
      rw [smul_mul_assoc, coe_mul_coe]
    _ ≤ #((s ∪ t) * Stab C) - #((s ∪ t) * Stab (coset C s a * coset C t b)) := by
      rw [← cast_ncard_sdiff (mul_subset_mul_left hst) ((hsfin.union htfin).mul hstabCfin)]
      gcongr Nat.cast #(?_)
      · exact ((hsfin.union htfin).mul hstabCfin).diff _
      refine fun x hx ↦ ⟨?_, ?_⟩
      · apply smul_set_subset_mul (mem_union_left t has) hx.1
      have hx' := hx.2
      contrapose! hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := hx.1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • Stab C := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_set_iff, ← coe_mul_coe]
        apply mul_mem_mul hc (mem_stabilizer_iff.mpr (inv_smul_eq_iff.mpr _))
        exact (mem_stabilizer_iff.mp (hst hd)).symm
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp hyst
        contrapose! hsC
        exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul ⟨hyst, hyC⟩ hd

@[to_additive]
lemma inter_mul_sub_card_le {a : G} {s t C : Set G} (has : a ∈ s) (hC : C.Nonempty)
    (hst : Stab (coset C s a * coset C t a) ⊆ Stab C) :
    (#(Stab C) : ℤ) - #(coset C s a * Stab (coset C s a * coset C t a)) -
        #(↑t ∩ a • Stab C * Stab (coset C s a * coset C t a)) ≤
      #((s ∪ t) * Stab C) - #((s ∪ t) * Stab (coset C s a * coset C t a)) := by
  calc
    (#(Stab C) : ℤ) - #(coset C s a * Stab (coset C s a * coset C t a)) -
      #(t ∩ a • Stab C * Stab (coset C s a * coset C t a)) ≤
        #(a • Stab C \ ((coset C s a ∪ t ∩ a • Stab C) * Stab (coset C s a * coset C t a))) := by
      rw [cast_ncard_sdiff, ncard_smul_set]
      · rw [union_mul, le_sub_iff_add_le]
        refine le_trans (add_le_add_left (Int.ofNat_le.mpr $ card_union_le _ _) _) ?_
        norm_num
      all_goals
        apply subset_trans (mul_subset_mul_left hst)
        rw [← union_inter_distrib_right]
        refine subset_trans (mul_subset_mul_right inter_subset_right) ?_
        simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * Stab C) -
          #((s ∪ t) * Stab (coset C s a * coset C t a)) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff (mul_subset_mul_left hst)]
      norm_cast
      apply card_le_card
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose! hx'
      rw [← union_inter_distrib_right]
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • Stab C := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_stabilizer_iff hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_stabilizer_iff hC).mp (hst hd))
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

end Set

variable [DecidableEq G] {s s' t t' C : Set G} {a b : G}

namespace Finset

set_option linter.dupNamespace false in
@[to_additive]
private lemma card_mul_add_card_lt (hC : C.Nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hCst : C ⊆ s * t) (hCst' : Disjoint C (s' * t')) :
    #(s' * t') + #s' < #(s * t) + #s :=
  add_lt_add_of_lt_of_le
      (by
        rw [← tsub_pos_iff_lt, ← card_sdiff (mul_subset_mul hs ht), card_pos]
        exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩)) $
    card_le_card hs

/-! ### Kneser's theorem -/

variable (s t)

/-- **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
stabilizer. -/
@[to_additive "**Kneser's addition theorem**: A lower bound on the size of `s + t` in terms of its
stabilizer."]
theorem mul_kneser :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by
  -- We're doing induction on `#(s * t) + #s` generalizing the group. This is a bit tricky
  -- in Lean.
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction' n using Nat.strong_induction_on with n ih generalizing G
  subst hn
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
  -- We distinguish whether `s * t` has trivial stabilizer.
  obtain hstab | hstab := ne_or_eq (s * t).mulStab 1
  · have image_coe_mul :
      ((s * t).image (↑) : Finset (α ⧸ stabilizer α (s * t).toSet)) = s.image (↑) * t.image (↑) :=
      image_mul (QuotientGroup.mk' _ : α →* α ⧸ stabilizer α (s * t).toSet)
    suffices hineq :
      #(s * t).mulStab *
          (#(s.image (↑) : Finset (α ⧸ stabilizer α (s * t).toSet)) +
              #(t.image (↑) : Finset (α ⧸ stabilizer α (s * t).toSet)) -  1) ≤
        #(s * t) by
    -- now to prove that `#(s * (s * t).mulStab) = #(s * t).mulStab * #(s.image (↑))` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
      rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mulStab_mul_card_image_coe',
        card_mulStab_mul_card_image_coe'] at hineq
      convert hineq using 1
      exact add_comm _ _
    refine le_of_le_of_eq (mul_le_mul_left' ?_ _) (card_mul_card_eq_mulStab_card_mul_coe s t).symm
    have := ih _ ?_ (s.image (↑) : Finset (α ⧸ stabilizer α (s * t).toSet)) (t.image (↑)) rfl
    · classical
      simpa only [← image_coe_mul, mulStab_image_coe_quotient (hs.mul ht), mul_one,
        tsub_le_iff_right, card_one] using this
    rw [← image_coe_mul, card_mul_card_eq_mulStab_card_mul_coe]
    exact
      add_lt_add_of_lt_of_le
        (lt_mul_left ((hs.mul ht).image _).card_pos $
          Finset.one_lt_card.2 ((hs.mul ht).mulStab_nontrivial.2 hstab))
        card_image_le
  -- Simplify the induction hypothesis a bit. We will only need it over `G` from now on.
  simp only [hstab, mul_one, card_one] at ih ⊢
  replace ih := fun s' t' h => @ih _ h G _ _ s' t' rfl
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · rw [card_singleton, card_singleton_mul, add_comm]
  have : b / a ∉ t.mulStab := by
    refine fun h => hab (Eq.symm (eq_of_div_eq_one ?_))
    replace h := subset_mulStab_mul_right hs h
    rw [hstab, mem_one] at h
    exact h
  simp only [mem_stabilizer_iff' ht, smul_eq_mul, Classical.not_forall, exists_prop] at this
  obtain ⟨c, hc, hbac⟩ := this
  set t' := (a / c) • t with ht'
  clear_value t'
  rw [← inv_smul_eq_iff] at ht'
  subst ht'
  rename' t' => t
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel] at hc
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ← mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac
  rw [smul_finset_nonempty] at ht
  simp only [mul_smul_comm, smul_mul_assoc, mulStab_smul, card_smul_finset] at *
  have hst : (s ∩ t).Nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left, not_subset.2 ⟨_, hb, fun h => hbac $ inter_subset_right h⟩⟩
  clear! a b
  set convergent : Set (Finset G) :=
    {C | C ⊆ s * t ∧ #(s ∩ t) + #((s ∪ t) * Stab C) ≤ #C + #(Stab C)}
  have convergent_nonempty : convergent.Nonempty := by
    refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_right (card_le_card $
      subset_mul_left _ $ one_mem_stabilizer_iff.2 $ hst.mul $ hs.mono subset_union_left) _).trans $
        ih (s ∩ t) (s ∪ t) ?_⟩
    exact add_lt_add_of_le_of_lt (card_le_card inter_mul_union_subset) (card_lt_card hsts)
  let C := argminOn (fun C : Finset α => #(Stab C)) _ convergent_nonempty
  set H := #(Stab C) with hH
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argminOn_mem _ _ _
  have hCmin (D : Finset α) (hDH : Stab D ⊂ H) : D ∉ convergent := fun hD ↦
    (card_lt_card hDH).not_le $ argminOn_le (fun D : Finset α => #(Stab D)) _ hD
  clear_value C
  clear convergent_nonempty
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp [hst.ne_empty, hH] at hCcard
  -- If the stabilizer of `C` is trivial, then
  -- `#s + #t - 1 = #(s ∩ t) + #(s ∪ t) - 1 = ≤ #C ≤ #(s * t)`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_stabilizer_iff.2 hC)
  · simp only [hH, hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard
    exact hCcard.trans (add_le_add_right (card_le_card hCst) _)
  exfalso
  have : ¬s * t * H ⊆ s * t := by
    rw [mul_subset_left_iff (hs.mul ht), hstab, ← coe_subset, coe_one]
    exact hCstab.coe.not_subset_singleton
  simp_rw [mul_subset_iff_left, Classical.not_forall, mem_mul] at this
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hab⟩ := this
  set s₁ := s ∩ a • H with hs₁
  set s₂ := s ∩ b • H with hs₂
  set t₁ := t ∩ b • H with ht₁
  set t₂ := t ∩ a • H with ht₂
  have hs₁s : s₁ ⊆ s := inter_subset_left
  have hs₂s : s₂ ⊆ s := inter_subset_left
  have ht₁t : t₁ ⊆ t := inter_subset_left
  have ht₂t : t₂ ⊆ t := inter_subset_left
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_stabilizer_iff.2 hC, mul_one _⟩⟩
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_stabilizer_iff.2 hC, mul_one _⟩⟩
  have hs₁ne : s₁.Nonempty := ⟨_, has₁⟩
  have ht₁ne : t₁.Nonempty := ⟨_, hbt₁⟩
  set C₁ := C ∪ s₁ * t₁
  set C₂ := C ∪ s₂ * t₂
  set H₁ := (s₁ * t₁).mulStab with hH₁
  set H₂ := (s₂ * t₂).mulStab
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t)
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t)
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm, mul_comm s₂ t₂]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_stabilizer hCst hab)
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_stabilizer hCst hab)
  have hst₁ : #(s₁ * t₁) + #s₁ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁
  have hst₂ : #(s₂ * t₂) + #s₂ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂
  have hC₁stab : C₁.mulStab = H₁ := stabilizer_union_mul_eq_stabilizer_mul hs₁ne ht₁ne hab hCst₁
  have hH₁H : H₁ ⊂ H := stabilizer_mul_ssubset_stabilizer hs₁ne ht₁ne hab
  have aux1₁ :=
    mul_aux1 (ih _ _ hst₁) hCcard
      (not_le.1 fun h => hCmin _ (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hCst₁
  obtain ht₂ | ht₂ne := t₂.eq_empty_or_nonempty
  · have aux₁_contr :=
      disjoint_mul_sub_card_le b (hs₁s has₁) (disjoint_iff_inter_eq_empty.2 ht₂) hH₁H.subset
    linarith [aux1₁, aux₁_contr, Int.natCast_nonneg #(t₁ * (s₁ * t₁).mulStab)]
  obtain hs₂ | hs₂ne := s₂.eq_empty_or_nonempty
  · have aux1₁_contr :
      (#C.mulStab : ℤ) - #(t₁ * (s₁ * t₁).mulStab) ≤
        #((s ∪ t) * C.mulStab) - #((s ∪ t) * (s₁ * t₁).mulStab) := by
      simpa [union_comm, mul_comm s₁ t₁] using
        disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.2 hs₂)
          (by rw [mul_comm]; exact hH₁H.subset)
    simp only [union_comm t s, mul_comm t₁ s₁] at aux1₁_contr
    linarith [aux1₁, aux1₁_contr, Int.natCast_nonneg #(s₁ * (s₁ * t₁).mulStab)]
  have hC₂stab : C₂.mulStab = H₂ := stabilizer_union_mul_eq_stabilizer_mul hs₂ne ht₂ne (by rwa [mul_comm]) hCst₂
  have hH₂H : H₂ ⊂ H := stabilizer_mul_ssubset_stabilizer hs₂ne ht₂ne (by rwa [mul_comm])
  have aux1₂ :=
    mul_aux1 (ih _ _ hst₂) hCcard
      (not_le.1 fun h => hCmin _ (hC₂stab.trans_ssubset hH₂H) ⟨hC₂st, h⟩) hC₂stab hCst₂
  obtain habH | habH := eq_or_ne (a • H) (b • H)
  · simp only [← habH] at aux1₁
    rw [hH₁, hs₁, ht₁, ← habH, hH] at hH₁H
    refine aux1₁.not_le ?_
    simp only [hs₁, ht₁, ← habH, inter_mul_sub_card_le (hs₁s has₁) hH₁H.subset, H]
  -- temporarily skipping deduction of inequality (2)
  set S := a • H \ (s₁ ∪ t₂) with hS
  set T := b • H \ (s₂ ∪ t₁) with hT
  have hST : Disjoint S T :=
    (C.pairwiseDisjoint_smul_finset_mulStab (Set.mem_range_self _) (Set.mem_range_self _)
          habH).mono
      sdiff_le sdiff_le
  have hSst : S ⊆ a • H \ (s ∪ t) := by
    simp only [hS, hs₁, ht₂, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hTst : T ⊆ b • H \ (s ∪ t) := by
    simp only [hT, hs₂, ht₁, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hSTst : Disjoint (S ∪ T) (s ∪ t) := (subset_sdiff.1 hSst).2.sup_left (subset_sdiff.1 hTst).2
  have hstconv : s * t ∉ convergent := by
    apply hCmin (s * t)
    rw [hstab]
    refine (hStab C_nontrivial.mp hCstab).symm.ssubset_of_subset ?_
    simp only [one_subset, one_mem_stabilizer_iff, hC]
  simp only [Set.mem_setOf_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
    convergent] at hstconv
  zify at hstconv
  have hSTcard : (#S : ℤ) + #T + #(s ∪ t) ≤ #((s ∪ t) * H) := by
    norm_cast
    conv_lhs => rw [← card_union_of_disjoint hST, ← card_union_of_disjoint hSTst, ← mul_one (s ∪ t)]
    refine card_le_card
      (union_subset (union_subset ?_ ?_) $ mul_subset_mul_left $ one_subset.2 hC.one_mem_stabilizer_iff)
    · exact hSst.trans (sdiff_subset.trans $ smul_finset_subset_smul $ mem_union_left _ ha)
    · exact hTst.trans (sdiff_subset.trans $ smul_finset_subset_smul $ mem_union_right _ hb)
  have hH₁ne : H₁.Nonempty := (hs₁ne.mul ht₁ne).mulStab
  have hH₂ne : H₂.Nonempty := (hs₂ne.mul ht₂ne).mulStab
  -- Now we prove inequality (2)
  have aux2₁ : (#s₁ : ℤ) + #t₁ + #H₁ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le $ Nat.cast_le.2 $ card_le_card $
      mul_subset_mul_left hH₁H.subset).trans_lt aux1₁) $ dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₁ne.mul ht₁ne) hH₁H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) $
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    gcongr _ - (Nat.cast ?_ + Nat.cast ?_) <;> exact card_le_card_mul_right hH₁ne
  have aux2₂ : (#s₂ : ℤ) + #t₂ + #H₂ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le $ Nat.cast_le.2 $ card_le_card $
      mul_subset_mul_left hH₂H.subset).trans_lt aux1₂) $ dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₂ne.mul ht₂ne) hH₂H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) $
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    exact sub_le_sub_left (add_le_add (Nat.cast_le.2 $ card_le_card_mul_right hH₂ne) $
      Nat.cast_le.2 $ card_le_card_mul_right hH₂ne) _
  -- Now we deduce inequality (3) using the above lemma in addition to the facts that `s * t` is not
  -- convergent and then induction hypothesis applied to `sᵢ` and `tᵢ`
  have aux3₁ : (#S : ℤ) + #T + #s₁ + #t₁ - #H₁ < #H :=
    calc
      (#S : ℤ) + #T + #s₁ + #t₁ - #H₁
        < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₁ * t₁) := by
        have ih₁ :=
          (add_le_add (card_le_card_mul_right hH₁ne) $ card_le_card_mul_right hH₁ne).trans
            (ih _ _ hst₁)
        zify at ih₁
        linarith [hstconv, ih₁]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₁ * t₁) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₁] using card_le_card hC₁st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.ofNat_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard

  have aux3₂ : (#S : ℤ) + #T + #s₂ + #t₂ - #H₂ < #H :=
    calc
      (#S : ℤ) + #T + #s₂ + #t₂ - #H₂
       < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₂ * t₂) := by
        have ih₂ :=
          (add_le_add (card_le_card_mul_right hH₂ne) $ card_le_card_mul_right hH₂ne).trans
            (ih _ _ hst₂)
        zify at hstconv ih₂
        linarith [ih₂]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₂ * t₂) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₂] using card_le_card hC₂st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.ofNat_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux4₁ : #H ≤ #S + (#s₁ + #t₂) := by
    rw [← card_smul_finset a H]
    exact card_le_card_sdiff_add_card.trans (add_le_add_left (card_union_le _ _) _)
  have aux4₂ : #H ≤ #T + (#s₂ + #t₁) := by
    rw [← card_smul_finset b H]
    exact card_le_card_sdiff_add_card.trans (add_le_add_left (card_union_le _ _) _)
  linarith [aux2₁, aux2₂, aux3₁, aux3₂, aux4₁, aux4₂]

/-- The strict version of **Kneser's multiplication theorem**. If the LHS of `Finset.mul_kneser`
does not equal the RHS, then it is in fact much smaller. -/
@[to_additive "The strict version of **Kneser's addition theorem**. If the LHS of
`Finset.add_kneser` does not equal the RHS, then it is in fact much smaller."]
lemma mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) :=
  Nat.le_of_lt_add_of_dvd h
      ((card_mulStab_dvd_card_mul_mulStab _ _).add $ card_mulStab_dvd_card_mul_mulStab _ _) $
    card_mulStab_dvd_card _

end Finset
