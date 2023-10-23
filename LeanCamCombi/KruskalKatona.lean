/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sups
import Mathlib.Combinatorics.SetFamily.Compression.UV
import LeanCamCombi.Mathlib.Combinatorics.Colex
import LeanCamCombi.Mathlib.Combinatorics.SetFamily.Shadow
import LeanCamCombi.Mathlib.Order.RelClasses

/-!
# Kruskal-Katona theorem

The Kruskal-Katona theorem in a few different versions, and an application to
the Erdos-Ko-Rado theorem.

The key results proved here are:

* The basic Kruskal-Katona theorem, expressing that given a set family 𝒜
  consisting of `r`-sets, and 𝒞 an initial segment of the wolex order of the
  same size, the shadow of 𝒞 is smaller than the shadow of 𝒜.
  In particular, this shows that the minimum shadow size is achieved by initial
  segments of wolex.

lemma kruskal_katona {r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))} (h₁ : (𝒜 : set (Finset α)).Sized r)
  (h₂ : 𝒜.card = 𝒞.card) (h₃ : IsInitSeg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=

* A strengthened form, giving the same result under a weaker constraint.

lemma strengthened_kk {r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))} (h₁ : (𝒜 : set (Finset α)).Sized r)
  (h₂ : 𝒞.card ≤ 𝒜.card) (h₃ : IsInitSeg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=

* An iterated form, giving that the minimum iterated shadow size is given
  by initial segments of wolex.

lemma iterated_kk {r k : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))} (h₁ : (𝒜 : set (Finset α)).Sized r)
  (h₂ : 𝒞.card ≤ 𝒜.card) (h₃ : IsInitSeg 𝒞 r) :
  (∂^[k] 𝒞).card ≤ (∂^[k] 𝒜).card :=

* A special case of iterated_kk which is often more practical to use.

lemma lovasz_form {r k i : ℕ} {𝒜 : Finset (Finset (Fin n))} (hir : i ≤ r)
  (hrk : r ≤ k) (hkn : k ≤ n) (h₁ : (𝒜 : set (Finset α)).Sized r) (h₂ : choose k r ≤ 𝒜.card) :
  choose k (r-i) ≤ (∂^[i] 𝒜).card :=

* Erdos-Ko-Rado theorem, giving the upper bound on the size of an intersecting
  family of `r`-sets

lemma EKR {𝒜 : Finset (Finset (Fin n))} {r : ℕ}
  (h₁ : intersecting 𝒜) (h₂ : (𝒜 : set (Finset α)).Sized r) (h₃ : r ≤ n/2) :
  𝒜.card ≤ choose (n-1) (r-1) :=

## TODO

* Define the `k`-cascade representation of a natural and prove the corresponding version of
  Kruskal-Katona.
* Abstract away from `Fin n` so that it also applies to `ℕ`. Probably `LocallyFiniteOrderBot`
  will help here.
* Characterise the equality case.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

kruskal-katona, kruskal, katona, shadow, initial segments, intersecting
-/

open Nat
open scoped FinsetFamily

namespace Finset
namespace Wolex
variable {α : Type*} [LinearOrder α] {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)} {s t : Finset α} {r : ℕ}

/-- This is important for iterating Kruskal-Katona: the shadow of an initial segment is also an
initial segment. -/
lemma shadow_initSeg [Fintype α] (hs : s.Nonempty) :
    ∂ (initSeg s) = initSeg (erase s $ min' s hs) := by
  -- This is a pretty painful proof, with lots of cases.
  ext t
  simp only [mem_shadow_iff_insert_mem, mem_initSeg, exists_prop]
  constructor
  -- First show that if t ∪ i ≤ s, then t ≤ s - min s
  · rintro ⟨i, ih, p, hts⟩
    rw [card_insert_of_not_mem ih] at p
    rw [toWolex_le_toWolex] at hts
    have cards : (erase s $ min' s hs).card = t.card := by
      rw [card_erase_of_mem (min'_mem _ _), p, add_tsub_cancel_right]
    -- Case on t ∪ i = s or t ∪ i < s
    obtain rfl | ⟨k, z, hkt, hks⟩ := hts
    · -- Case on i = min s or not
      refine' ⟨cards, le_def.2 $ (eq_or_ne i $ min' _ hs).imp (fun q => _) fun q ↦ _⟩
      · rw [←q, erase_insert ih]
      · refine' ⟨i, fun x hx ↦ _, ih, mem_erase.2 ⟨q, mem_insert_self _ _⟩⟩
        simpa only [ofWolex_toWolex, mem_erase, mem_insert, hx.ne', Ne.def, false_or_iff,
          iff_and_self] using fun _ ↦ ((min'_le _ _ $ mem_insert_self _ _).trans_lt hx).ne'
    · simp only [cards, eq_self_iff_true, true_and_iff, mem_insert, not_or, ←Ne.def] at hkt hks z ⊢
      -- t ∪ i < s, with k as the wolex witness. Cases on k < i or k > i.
      obtain h | h := hkt.1.lt_or_lt
      · refine' Or.inr ⟨i, fun x hx ↦ _, ih, _⟩
        -- When k < i, then i works as the wolex witness to show t < s - min s
        · refine' ⟨fun p ↦ mem_erase_of_ne_of_mem (((min'_le _ _ ‹_›).trans_lt h).trans hx).ne'
            ((z $ h.trans hx).1 $ Or.inr p), fun p ↦ _⟩
          exact ((z $ h.trans hx).2 $ mem_of_mem_erase p).resolve_left hx.ne'
        apply mem_erase_of_ne_of_mem _ ((z h).1 $ Or.inl rfl)
        refine (lt_of_le_of_lt ?_ h).ne'
        apply min'_le
        assumption
      · -- When k > i, cases on min s < k or min s = k
        obtain h₁ | h₁ := (min'_le _ _ ‹k ∈ s›).lt_or_eq
        -- If min s < k, k works as the wolex witness for t < s - min s
        · refine' Or.inr ⟨k, fun x hx ↦ _, hkt.2, mem_erase_of_ne_of_mem (ne_of_gt h₁) ‹_›⟩
          simpa [(h.trans hx).ne', ←z hx] using fun _ ↦ (h₁.trans hx).ne'
        -- If k = min s, then t = s - min s
        -- TODO: In Lean 3, this was `generalize_proofs at h₁`
        set h : ∃ x, x ∈ s := ⟨_, hks⟩
        clear_value h
        subst h₁
        refine' Or.inl (eq_of_subset_of_card_le (fun a ha ↦ _) cards.ge).symm
        rw [mem_erase] at ha
        have : a ≠ i := ne_of_gt (lt_of_lt_of_le h $ min'_le _ _ ha.2)
        rw [←z] at ha
        apply ha.2.resolve_left ‹a ≠ i›
        exact (min'_le _ _ ha.2).lt_of_ne ha.1.symm
  -- Now show that if t ≤ s - min s, there is j such that t ∪ j ≤ s
  -- We choose j as the smallest thing not in t
  simp_rw [le_def]
  simp only [toWolex_inj, ofWolex_toWolex, ne_eq, and_imp]
  rintro cards' (rfl | ⟨k, z, hkt, hks⟩)
  -- If t = s - min s, then use j = min s so t ∪ j = s
  · refine' ⟨min' s hs, not_mem_erase _ _, _⟩
    rw [insert_erase (min'_mem _ _)]
    exact ⟨rfl, Or.inl rfl⟩
  set j := min' tᶜ ⟨k, mem_compl.2 hkt⟩
  -- Assume first t < s - min s, and take k as the wolex witness for this
  have hjk : j ≤ k := min'_le _ _ (mem_compl.2 ‹k ∉ t›)
  have : j ∉ t := mem_compl.1 (min'_mem _ _)
  have cards : card s = card (insert j t) := by
    rw [card_insert_of_not_mem ‹j ∉ t›, ←‹_ = card t›, card_erase_add_one (min'_mem _ _)]
  refine' ⟨j, ‹_›, cards, _⟩
  -- Cases on j < k or j = k
  obtain hjk | r₁ := hjk.lt_or_eq
  -- if j < k, k is our wolex witness for t ∪ {j} < s
  · refine' Or.inr ⟨k, fun x hx ↦ _, fun hk ↦ hkt $ mem_of_mem_insert_of_ne hk hjk.ne',
      mem_of_mem_erase ‹_›⟩
    simpa only [mem_insert, z hx, (hjk.trans hx).ne', mem_erase, Ne.def, false_or_iff,
      and_iff_right_iff_imp] using fun _ ↦ ((min'_le _ _ $ mem_of_mem_erase hks).trans_lt hx).ne'
  -- if j = k, all of range k is in t so by sizes t ∪ {j} = s
  refine' Or.inl (eq_of_subset_of_card_le (fun a ha ↦ _) cards.ge).symm
  rcases lt_trichotomy k a with (lt | rfl | gt)
  · apply mem_insert_of_mem
    rw [z lt]
    refine' mem_erase_of_ne_of_mem (lt_of_le_of_lt _ lt).ne' ha
    apply min'_le _ _ (mem_of_mem_erase ‹_›)
  · rw [r₁]; apply mem_insert_self
  · apply mem_insert_of_mem
    rw [←r₁] at gt
    by_contra
    apply (min'_le tᶜ _ _).not_lt gt
    rwa [mem_compl]

/-- The shadow of an initial segment is also an initial segment. -/
protected lemma IsInitSeg.shadow [Finite α] (h₁ : IsInitSeg 𝒜 r) : IsInitSeg (∂ 𝒜) (r - 1) := by
  cases nonempty_fintype α
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · have : 𝒜 ⊆ {∅} := fun s hs ↦ by rw [mem_singleton, ←Finset.card_eq_zero]; exact h₁.1 hs
    have := shadow_monotone this
    simp only [subset_empty, le_eq_subset, shadow_singleton_empty] at this
    simp [this]
  obtain rfl | h𝒜 := 𝒜.eq_empty_or_nonempty
  · simp
  obtain ⟨s, rfl, rfl⟩ := h₁.exists_initSeg h𝒜
  rw [shadow_initSeg (card_pos.1 hr), ←card_erase_of_mem (min'_mem _ _)]
  exact isInitSeg_initSeg

end Wolex

open Finset Wolex Nat UV
open scoped BigOperators FinsetFamily

variable {α : Type*} [LinearOrder α] {s U V : Finset α} {n : ℕ}

namespace UV

/-- Applying the compression makes the set smaller in wolex. This is intuitive since a portion of
the set is being "shifted 'down" as `max U < max V`. -/
lemma toWolex_compress_lt_toWolex {hU : U.Nonempty} {hV : V.Nonempty} (h : max' U hU < max' V hV)
    (hA : compress U V s ≠ s) : toWolex (compress U V s) < toWolex s := by
  rw [compress, ite_ne_right_iff] at hA
  rw [compress, if_pos hA.1, lt_def]
  refine'
    ⟨max' V hV, fun a ha ↦ _, not_mem_sdiff_of_mem_right $ max'_mem _ _, hA.1.2 $ max'_mem _ _⟩
  have : a ∉ V := fun H ↦ ha.not_le (le_max' _ _ H)
  have : a ∉ U := fun H ↦ ha.not_lt ((le_max' _ _ H).trans_lt h)
  simp [‹a ∉ U›, ‹a ∉ V›]

/-- These are the compressions which we will apply to decrease the "measure" of a family of sets.-/
private def UsefulCompression (U V : Finset α) : Prop :=
  Disjoint U V ∧ U.card = V.card ∧ ∃ (HU : U.Nonempty) (HV : V.Nonempty), max' U HU < max' V HV

instance UsefulCompression.instDecidableRel : @DecidableRel (Finset α) UsefulCompression :=
  fun _U _V ↦ And.decidable

/-- Applying a good compression will decrease measure, keep cardinality, keep sizes and decrease
shadow. In particular, 'good' means it's useful, and every smaller compression won't make a
difference. -/
lemma compression_improved (𝒜 : Finset (Finset α)) (h₁ : UsefulCompression U V)
    (h₂ : ∀ ⦃U₁ V₁⦄, UsefulCompression U₁ V₁ → U₁.card < U.card → IsCompressed U₁ V₁ 𝒜) :
    (∂ (𝓒 U V 𝒜)).card ≤ (∂ 𝒜).card := by
  obtain ⟨UVd, same_size, hU, hV, max_lt⟩ := h₁
  refine' card_shadow_compression_le _ _ fun x Hx ↦ ⟨min' V hV, min'_mem _ _, _⟩
  obtain hU' | hU' := eq_or_lt_of_le (succ_le_iff.2 hU.card_pos)
  · rw [←hU'] at same_size
    have : erase U x = ∅ := by rw [←Finset.card_eq_zero, card_erase_of_mem Hx, ←hU']
    have : erase V (min' V hV) = ∅ := by
      rw [←Finset.card_eq_zero, card_erase_of_mem (min'_mem _ _), ←same_size]
    rw [‹erase U x = ∅›, ‹erase V (min' V hV) = ∅›]
    exact isCompressed_self _ _
  refine' h₂ ⟨UVd.mono (erase_subset _ _) (erase_subset _ _), _, _, _, _⟩ (card_erase_lt_of_mem Hx)
  · rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size]
  · rwa [←card_pos, card_erase_of_mem Hx, tsub_pos_iff_lt]
  · rwa [←Finset.card_pos, card_erase_of_mem (min'_mem _ _), ←same_size, tsub_pos_iff_lt]
  · refine' (Finset.max'_subset _ $ erase_subset _ _).trans_lt (max_lt.trans_le $
      le_max' _ _ $ mem_erase.2 ⟨(min'_lt_max'_of_card _ _).ne', max'_mem _ _⟩)
    rwa [←same_size]

/-- If we're compressed by all useful compressions, then we're an initial segment. This is the other
key Kruskal-Katona part. -/
lemma isInitSeg_of_compressed {ℬ : Finset (Finset α)} {r : ℕ} (h₁ : (ℬ : Set (Finset α)).Sized r)
    (h₂ : ∀ U V, UsefulCompression U V → IsCompressed U V ℬ) : IsInitSeg ℬ r := by
  refine' ⟨h₁, _⟩
  rintro A B hA ⟨hBA, sizeA⟩
  by_contra hB
  have hAB : A ≠ B := ne_of_mem_of_not_mem hA hB
  have hAB' : A.card = B.card := (h₁ hA).trans sizeA.symm
  have hU : (A \ B).Nonempty := sdiff_nonempty.2 fun h ↦ hAB $ eq_of_subset_of_card_le h hAB'.ge
  have hV : (B \ A).Nonempty :=
    sdiff_nonempty.2 fun h ↦ hAB.symm $ eq_of_subset_of_card_le h hAB'.le
  have disj : Disjoint (B \ A) (A \ B) := disjoint_sdiff.mono_left (sdiff_subset _ _)
  have smaller : max' _ hV < max' _ hU := by
    obtain hlt | heq | hgt := lt_trichotomy (max' _ hU) (max' _ hV)
    · rw [←compress_sdiff_sdiff A B] at hAB hBA
      cases hBA.not_lt $ toWolex_compress_lt_toWolex hlt hAB
    · exact (disjoint_right.1 disj (max'_mem _ hU) $ heq.symm ▸ max'_mem _ _).elim
    · assumption
  refine' hB _
  rw [←(h₂ _ _ ⟨disj, card_sdiff_comm hAB'.symm, hV, hU, smaller⟩).eq]
  exact mem_compression.2 (Or.inr ⟨hB, A, hA, compress_sdiff_sdiff _ _⟩)

attribute [-instance] Fintype.decidableForallFintype

-- TODO: There's currently a diamond
-- import Mathlib.Data.Fin.Basic
-- example (n : ℕ) : instDecidableEqFin n = instDecidableEq := rfl
attribute [-instance] instDecidableEqFin

/-- This measures roughly how compressed the family is. (Note that it does depend on the order of
the ground set, unlike Kruskal-Katona itself). -/
private def familyMeasure (𝒜 : Finset (Finset (Fin n))) : ℕ := ∑ A in 𝒜, ∑ a in A, 2 ^ (a : ℕ)

/-- Applying a compression strictly decreases the measure. This helps show that "compress until we
can't any more" is a terminating process. -/
lemma familyMeasure_compression_lt_familyMeasure {U V : Finset (Fin n)} {hU : U.Nonempty}
    {hV : V.Nonempty} (h : max' U hU < max' V hV) {𝒜 : Finset (Finset (Fin n))} (a : 𝓒 U V 𝒜 ≠ 𝒜) :
    familyMeasure (𝓒 U V 𝒜) < familyMeasure 𝒜 := by
  rw [compression] at a ⊢
  have q : ∀ Q ∈ 𝒜.filter fun A ↦ compress U V A ∉ 𝒜, compress U V Q ≠ Q := by
    simp_rw [mem_filter]
    intro Q hQ h
    rw [h] at hQ
    exact hQ.2 hQ.1
  have uA : (𝒜.filter fun A => compress U V A ∈ 𝒜) ∪ 𝒜.filter (fun A ↦ compress U V A ∉ 𝒜) = 𝒜 :=
    filter_union_filter_neg_eq _ _
  have ne₂ : (𝒜.filter fun A ↦ compress U V A ∉ 𝒜).Nonempty := by
    refine' nonempty_iff_ne_empty.2 fun z ↦ a _
    rw [image_filter, z, image_empty, union_empty]
    rwa [z, union_empty] at uA
  rw [familyMeasure, familyMeasure, sum_union compress_disjoint]
  conv_rhs => rw [←uA]
  rw [sum_union (disjoint_filter_filter_neg _ _ _), add_lt_add_iff_left, image_filter,
    sum_image compress_injOn]
  refine' sum_lt_sum_of_nonempty ne₂ fun A hA ↦ _
  simp_rw [←sum_image (Fin.val_injective.injOn _)]
  rw [sum_two_pow_lt_iff_wolex_lt, toWolex_image_lt_toWolex_image Fin.val_strictMono]
  convert toWolex_compress_lt_toWolex h ?_
  convert q _ hA

/-- The main Kruskal-Katona helper: use induction with our measure to keep compressing until
we can't any more, which gives a set family which is fully compressed and has the nice properties we
want. -/
private lemma kruskal_katona_helper {r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h : (𝒜 : Set (Finset (Fin n))).Sized r) :
    ∃ ℬ : Finset (Finset (Fin n)), (∂ ℬ).card ≤ (∂ 𝒜).card ∧ 𝒜.card = ℬ.card ∧
      (ℬ : Set (Finset (Fin n))).Sized r ∧ ∀ U V, UsefulCompression U V → IsCompressed U V ℬ := by
  classical
  revert h
  apply WellFounded.recursion (InvImage.wf familyMeasure wellFounded_lt) 𝒜
  intro A ih h
  -- Are there any compressions we can make now?
  set usable : Finset (Finset (Fin n) × Finset (Fin n)) :=
    univ.filter fun t ↦ UsefulCompression t.1 t.2 ∧ ¬ IsCompressed t.1 t.2 A
  obtain husable | husable := usable.eq_empty_or_nonempty
  -- No. Then where we are is the required set family.
  · refine' ⟨A, le_rfl, rfl, h, fun U V hUV ↦ _⟩
    rw [eq_empty_iff_forall_not_mem] at husable
    by_contra h
    exact husable ⟨U, V⟩ $ mem_filter.2 ⟨mem_univ _, hUV, h⟩
  -- Yes. Then apply the compression, then keep going
  obtain ⟨⟨U, V⟩, hUV, t⟩ := exists_min_image usable (fun t ↦ t.1.card) husable
  rw [mem_filter] at hUV
  have h₂ : ∀ U₁ V₁, UsefulCompression U₁ V₁ → U₁.card < U.card → IsCompressed U₁ V₁ A := by
    rintro U₁ V₁ huseful hUcard
    by_contra h
    exact hUcard.not_le $ t ⟨U₁, V₁⟩ $ mem_filter.2 ⟨mem_univ _, huseful, h⟩
  have p1 : (∂ (𝓒 U V A)).card ≤ (∂ A).card := compression_improved _ hUV.2.1 h₂
  obtain ⟨-, hUV', hu, hv, hmax⟩ := hUV.2.1
  unfold InvImage at ih
  obtain ⟨t, q1, q2, q3, q4⟩ := ih (𝓒 U V A)
    (familyMeasure_compression_lt_familyMeasure hmax hUV.2.2) (h.uvCompression hUV')
  exact ⟨t, q1.trans p1, (card_compression _ _ _).symm.trans q2, q3, q4⟩

end UV

-- Finally we can prove Kruskal-Katona.
section KK

variable {r k i : ℕ} {𝒜 𝒞 : Finset $ Finset $ Fin n}

/-- The Kruskal-Katona theorem. It says that given a set family `𝒜` consisting of `r`-sets, and `𝒞`
an initial segment of the wolex order of the same size, the shadow of `𝒞` is smaller than the shadow
of `𝒜`. In particular, this gives that the minimum shadow size is achieved by initial segments of
wolex.

Proof notes: Most of the work was done in Kruskal-Katona helper; it gives a `ℬ` which is fully
compressed, and so we know it's an initial segment, which by uniqueness is the same as `𝒞`. -/
lemma kruskal_katona (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : 𝒜.card = 𝒞.card)
    (h₃ : IsInitSeg 𝒞 r) : (∂ 𝒞).card ≤ (∂ 𝒜).card := by
  obtain ⟨ℬ, card_le, t, hℬ, fully_comp⟩ := UV.kruskal_katona_helper 𝒜 h₁
  convert card_le
  have hcard : card ℬ = card 𝒞 := t.symm.trans h₂
  obtain CB | BC :=
    h₃.total (UV.isInitSeg_of_compressed hℬ fun U V hUV ↦ by convert fully_comp U V hUV)
  · exact eq_of_subset_of_card_le CB hcard.le
  · exact (eq_of_subset_of_card_le BC hcard.ge).symm

/-- We can strengthen Kruskal-Katona slightly: note the middle and has been relaxed to a `≤`.
This shows that the minimum possible shadow size is attained by initial segments. -/
lemma strengthened_kk (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : 𝒞.card ≤ 𝒜.card)
    (h₃ : IsInitSeg 𝒞 r) : (∂ 𝒞).card ≤ (∂ 𝒜).card := by
  rcases exists_smaller_set 𝒜 𝒞.card h₂ with ⟨𝒜', prop, size⟩
  refine' (kruskal_katona (fun A hA ↦ h₁ (prop hA)) size h₃).trans (card_le_of_subset _)
  rw [shadow, shadow]
  apply shadow_monotone prop

/-- An iterated form of the Kruskal-Katona theorem. In particular, the minimum possible iterated
shadow size is attained by initial segments. -/
lemma iterated_kk (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : 𝒞.card ≤ 𝒜.card)
    (h₃ : IsInitSeg 𝒞 r) : (∂^[k] 𝒞).card ≤ (∂^[k] 𝒜).card := by
  induction' k with _k ih generalizing r 𝒜 𝒞
  · simpa
  · refine' ih h₁.shadow (strengthened_kk h₁ h₂ h₃) _
    convert h₃.shadow

/-- A special case of Kruskal-Katona which is sometimes easier to work with.
If `|𝒜| ≥ k choose r`, (and everything in `𝒜` has size `r`) then the initial segment we compare to
is just all the subsets of `{0, ..., k - 1}` of size `r`. The `i`-th iterated shadow of this is all
the subsets of `{0, ..., k - 1}` of size `r - i`, so the `i`-th iterated shadow of `𝒜` has at least
`k.choose (r - i)` elements. -/
lemma lovasz_form (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h₁ : (𝒜 : Set (Finset $ Fin n)).Sized r) (h₂ : k.choose r ≤ 𝒜.card) :
    k.choose (r - i) ≤ (∂^[i] 𝒜).card := by
  set range'k : Finset (Fin n) :=
    attachFin (range k) fun m ↦ by rw [mem_range]; apply forall_lt_iff_le.2 hkn
  set 𝒞 : Finset (Finset (Fin n)) := powersetCard r range'k
  have Ccard : 𝒞.card = k.choose r
  rw [card_powersetCard, card_attachFin, card_range]
  have : (𝒞 : Set (Finset (Fin n))).Sized r := Set.sized_powersetCard _ _
  suffices this : (∂^[i] 𝒞).card = k.choose  (r - i)
  · rw [←this]
    apply iterated_kk h₁ _ _
    rwa [Ccard]
    refine' ⟨‹_›, _⟩
    rintro A B hA ⟨HB₁, HB₂⟩
    rw [mem_powersetCard]
    refine' ⟨fun t ht ↦ _, ‹_›⟩
    rw [mem_attachFin, mem_range]
    have : toWolex (image Fin.val B) < toWolex (image Fin.val A) := by
      rwa [toWolex_image_lt_toWolex_image Fin.val_strictMono]
    apply Wolex.forall_lt_mono this.le _ t (mem_image.2 ⟨t, ht, rfl⟩)
    simp_rw [mem_image]
    rintro _ ⟨a, ha, q⟩
    rw [mem_powersetCard] at hA
    rw [←q, ←mem_range]
    have := hA.1 ha
    rwa [mem_attachFin] at this
  suffices ∂^[i] 𝒞 = powersetCard (r - i) range'k by
    rw [this, card_powersetCard, card_attachFin, card_range]
  ext B
  rw [mem_powersetCard, mem_shadow_iterate_iff_exists_sdiff]
  constructor
  · rintro ⟨A, Ah, BsubA, card_sdiff_i⟩
    rw [mem_powersetCard] at Ah
    refine' ⟨BsubA.trans Ah.1, _⟩
    symm
    rw [Nat.sub_eq_iff_eq_add hir, ←Ah.2, ←card_sdiff_i, ←card_disjoint_union disjoint_sdiff,
      union_sdiff_of_subset BsubA]
  rintro ⟨hBk, hB⟩
  have := exists_intermediate_set i ?_ hBk
  obtain ⟨C, BsubC, hCrange, cards⟩ := this
  rw [hB, ←Nat.add_sub_assoc hir, Nat.add_sub_cancel_left] at cards
  refine' ⟨C, _, BsubC, _⟩; rw [mem_powersetCard]; exact ⟨hCrange, cards⟩
  · rw [card_sdiff BsubC, cards, hB, Nat.sub_sub_self hir]
  · rwa [hB, card_attachFin, card_range, ←Nat.add_sub_assoc hir, Nat.add_sub_cancel_left]

end KK

/-- The **Erdős–Ko–Rado lemma**: The maximum size of an intersecting family in `α` where all sets
have size `r` is bounded by `(card α - 1).choose (r - 1)`. This bound is sharp. -/
lemma EKR {𝒜 : Finset (Finset (Fin n))} {r : ℕ} (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (h₂ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₃ : r ≤ n / 2) :
    𝒜.card ≤ (n - 1).choose (r - 1) := by
  -- Take care of the r=0 case first: it's not very interesting.
  cases' Nat.eq_zero_or_pos r with b h1r
  · convert Nat.zero_le _
    rw [Finset.card_eq_zero, eq_empty_iff_forall_not_mem]
    refine' fun A HA ↦ h𝒜 HA HA _
    rw [disjoint_self_iff_empty, ←Finset.card_eq_zero, ←b]
    exact h₂ HA
  refine' le_of_not_lt fun size ↦ _
  -- Consider 𝒜ᶜˢ = {sᶜ | s ∈ 𝒜}
  -- Its iterated shadow (∂^[n-2k] 𝒜ᶜˢ) is disjoint from 𝒜 by intersecting-ness
  have : Disjoint 𝒜 (∂^[n - 2 * r] 𝒜ᶜˢ) := disjoint_right.2 fun A hAbar hA ↦ by
    simp [mem_shadow_iterate_iff_exists_sdiff, mem_compls] at hAbar
    obtain ⟨C, hC, hAC, _⟩ := hAbar
    exact h𝒜 hA hC (disjoint_of_subset_left hAC disjoint_compl_right)
  have : r ≤ n := h₃.trans (Nat.div_le_self n 2)
  have : 1 ≤ n := ‹1 ≤ r›.trans ‹r ≤ n›
  -- We know the size of 𝒜ᶜˢ since it's the same size as 𝒜
  have z : (n - 1).choose (n - r) < 𝒜ᶜˢ.card := by
    rwa [card_compls, choose_symm_of_eq_add (tsub_add_tsub_cancel ‹r ≤ n› ‹1 ≤ r›).symm]
  -- and everything in 𝒜ᶜˢ has size n-r.
  have h𝒜bar : (𝒜ᶜˢ : Set (Finset (Fin n))).Sized (n - r) := by simpa using h₂.compls
  have : n - 2 * r ≤ n - r := by
    rw [tsub_le_tsub_iff_left ‹r ≤ n›]
    exact Nat.le_mul_of_pos_left zero_lt_two
  -- We can use the Lovasz form of Kruskal-Katona to get |∂^[n-2k] 𝒜ᶜˢ| ≥ (n-1) choose r
  have kk :=
    lovasz_form ‹n - 2 * r ≤ n - r› ((tsub_le_tsub_iff_left ‹1 ≤ n›).2 h1r) tsub_le_self h𝒜bar z.le
  have q : n - r - (n - 2 * r) = r := by
    rw [tsub_right_comm, Nat.sub_sub_self, two_mul]
    apply Nat.add_sub_cancel
    rw [mul_comm, ←Nat.le_div_iff_mul_le' zero_lt_two]
    exact h₃
  rw [q] at kk
  -- But this gives a contradiction: `n choose r < |𝒜| + |∂^[n-2k] 𝒜ᶜˢ|`
  have : n.choose r < (𝒜 ∪ ∂^[n - 2 * r] 𝒜ᶜˢ).card
  rw [card_disjoint_union ‹_›]
  convert lt_of_le_of_lt (add_le_add_left kk _) (add_lt_add_right size _) using 1
  convert Nat.choose_succ_succ _ _ using 3
  any_goals rwa [Nat.sub_one, Nat.succ_pred_eq_of_pos]
  apply this.not_le
  convert Set.Sized.card_le _
  · rw [Fintype.card_fin]
  rw [coe_union, Set.sized_union]
  refine' ⟨‹_›, _⟩
  convert h𝒜bar.shadow_iterate
  rw [q]

end Finset
