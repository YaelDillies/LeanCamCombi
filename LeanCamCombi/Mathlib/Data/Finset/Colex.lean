import Mathlib.Combinatorics.Colex
import Mathlib.Order.SupClosed
import LeanCamCombi.Mathlib.Data.Finset.Basic
import LeanCamCombi.Mathlib.Data.Finset.Slice

/-!
# Wolex

We define the wolex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The wolex ordering likes to avoid large values - In the special case of `ℕ`, it can be thought of as
the "binary" ordering. That is, order s based on `∑_{i ∈ s} 2^i`.
It's defined here in a slightly more general way, requiring only `LT α` in
the definition of wolex on `Finset α`. In the context of the Kruskal-Katona
lemma, we are interested in particular on how wolex behaves for sets of a
fixed size. If the size is 3, wolex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements

* Wolex order properties - linearity, decidability and so on.
* `Finset.Wolex.forall_lt_mono`: if `s < t` in wolex, and everything in `t` is `< a`, then
  everything in `s` is `< a`. This confirms the idea that an enumeration under wolex will exhaust
  all sets using elements `< a` before allowing `a` to be included.
* `FinsetoWolex t_image_lt_toWolex_image`: Strictly monotone functions preserve wolex.
* `Finset.sum_two_pow_le_iff_wolex_le`: wolex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## See also

Related files are:
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`.

## TODO

* Generalise `wolex.initSeg` so that it applies to `ℕ`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

wolex, wolexicographic, binary
-/

variable {α β : Type*}

open Finset
open scoped BigOperators

namespace Finset

/-- Type synonym of `Finset α` equipped with the wolexicographic order rather than the inclusion
order. -/
def Wolex (α) := Finset α

instance : Inhabited (Finset.Wolex α) := inferInstanceAs (Inhabited (Finset α))

/-- `toWolex` is the "identity" function between `Finset α` and `Finset.Wolex α`. -/
def toWolex : Finset α ≃ Wolex α := Equiv.refl _

/-- `ofWolex` is the "identity" function between `Finset.Wolex α` and `Finset α`. -/
def ofWolex : Wolex α ≃ Finset α := Equiv.refl _

@[simp] lemma toWolex_symm_eq : (@toWolex α).symm = ofWolex := rfl
@[simp] lemma ofWolex_symm_eq : (@ofWolex α).symm = toWolex := rfl
@[simp] lemma toWolex_ofWolex (s : Wolex α) : toWolex (ofWolex s) = s := rfl
@[simp] lemma ofWolex_toWolex (s : Finset α) : ofWolex (toWolex s) = s := rfl
-- Tagged `nolint simpNF` because eligible for `dsimp`
@[simp, nolint simpNF] lemma toWolex_inj {s t : Finset α} : toWolex s = toWolex t ↔ s = t := Iff.rfl
@[simp, nolint simpNF] lemma ofWolex_inj {s t : Wolex α} : ofWolex s = ofWolex t ↔ s = t := Iff.rfl
lemma toWolex_ne_toWolex {s t : Finset α} : toWolex s ≠ toWolex t ↔ s ≠ t := Iff.rfl
lemma ofWolex_ne_ofWolex {s t : Wolex α} : ofWolex s ≠ ofWolex t ↔ s ≠ t := Iff.rfl

/-- Recursor for `Wolex α`. -/
@[elab_as_elim]
def Wolex.rec {C : Wolex α → Sort*} (h : ∀ s, C (toWolex s)) : ∀ s, C s := h

namespace Wolex
section LT
variable [LT α] {s t : Finset α}

/-- `s` is less than `t` in the wolex ordering if the largest thing that's not in both sets is in t.
In other words, `max (s ∆ t) ∈ t` (if the maximum exists). -/
instance instLT : LT (Wolex α) :=
  ⟨λ s t ↦ ∃ a, (∀ ⦃x⦄, a < x → (x ∈ ofWolex s ↔ x ∈ ofWolex t)) ∧ a ∉ ofWolex s ∧ a ∈ ofWolex t⟩

/-- We can define (≤) in the obvious way. -/
instance instLE : LE (Wolex α) := ⟨λ s t ↦ s = t ∨ s < t⟩

lemma lt_def {s t : Wolex α} :
    s < t ↔ ∃ a, (∀ ⦃x⦄, a < x → (x ∈ ofWolex s ↔ x ∈ ofWolex t)) ∧ a ∉ ofWolex s ∧ a ∈ ofWolex t :=
  Iff.rfl

lemma le_def {s t : Wolex α} :
    s ≤ t ↔ s = t ∨
      ∃ a, (∀ ⦃x⦄, a < x → (x ∈ ofWolex s ↔ x ∈ ofWolex t)) ∧ a ∉ ofWolex s ∧ a ∈ ofWolex t :=
  Iff.rfl

lemma toWolex_lt_toWolex :
    toWolex s < toWolex t ↔ ∃ k, (∀ ⦃x⦄, k < x → (x ∈ s ↔ x ∈ t)) ∧ k ∉ s ∧ k ∈ t := Iff.rfl

lemma toWolex_le_toWolex :
    toWolex s ≤ toWolex t ↔ s = t ∨ ∃ k, (∀ ⦃x⦄, k < x → (x ∈ s ↔ x ∈ t)) ∧ k ∉ s ∧ k ∈ t :=
  Iff.rfl

instance instIsIrrefl : IsIrrefl (Wolex α) (· < ·) := ⟨by simp [lt_def]⟩

/-- Wolex doesn't care if you remove the other set -/
@[simp]
lemma sdiff_lt_sdiff_iff_lt [DecidableEq α] (s t : Finset α) :
    toWolex (s \ t) < toWolex (t \ s) ↔ toWolex s < toWolex t := by
  rw [toWolex_lt_toWolex, toWolex_lt_toWolex]
  refine' exists_congr λ k ↦ _
  simp only [mem_sdiff, not_and, Classical.not_not]
  constructor
  · rintro ⟨z, kAB, kB, kA⟩
    refine' ⟨λ x hx ↦ _, kA, kB⟩
    specialize z hx
    tauto
  · rintro ⟨z, kA, kB⟩
    refine' ⟨λ x hx => _, fun _ ↦ kB, kB, kA⟩
    rw [z hx]

end LT

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)} {s t : Finset α}
  {a b : α} {r : ℕ}

instance : IsStrictTotalOrder (Wolex α) (· < ·) where
  irrefl := irrefl_of (· < ·)
  trans s t u := by
    rintro ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩
    obtain h | h := (ne_of_mem_of_not_mem inB notinB).lt_or_lt
    · refine' ⟨k₂, λ x hx ↦ _, by rwa [k₁z h], inC⟩
      rw [←k₂z hx]
      exact k₁z (h.trans hx)
    · refine' ⟨k₁, λ x hx ↦ _, notinA, by rwa [←k₂z h]⟩
      rw [k₁z hx]
      exact k₂z (h.trans hx)
  trichotomous s t := by
    classical
    obtain rfl | hts := eq_or_ne t s
    · simp
    obtain ⟨k, hk, z⟩ := exists_max_image (ofWolex t ∆ ofWolex s) id (symmDiff_nonempty.2 hts)
    refine' (mem_symmDiff.1 hk).imp (λ hk => ⟨k, λ a ha ↦ _, hk.2, hk.1⟩) fun hk ↦
        Or.inr ⟨k, λ a ha ↦ _, hk.2, hk.1⟩ <;>
      simpa [mem_symmDiff, not_or, iff_iff_implies_and_implies, and_comm, not_imp_not]
        using not_imp_not.2 (z a) ha.not_le

instance instDecidableLT : @DecidableRel (Wolex α) (· < ·) := λ s t ↦
  decidable_of_iff'
    (∃ k ∈ ofWolex t,
      (∀ x ∈ ofWolex s ∪ ofWolex t, k < x → (x ∈ ofWolex s ↔ x ∈ ofWolex t)) ∧ k ∉ ofWolex s) $
    exists_congr λ a ↦ by
      simp only [mem_union, exists_prop, or_imp, @and_comm (_ ∈ ofWolex t), and_assoc]
      exact and_congr_left' $ forall_congr' $ by tauto

instance instLinearOrder : LinearOrder (Wolex α) := linearOrderOfSTO (· < ·)

instance instBot : Bot (Wolex α) where
  bot := toWolex ∅

@[simp] lemma toWolex_empty : toWolex (∅ : Finset α) = ⊥ := rfl
@[simp] lemma ofWolex_bot : ofWolex (⊥ : Wolex α) = ∅ := rfl

instance instOrderBot : OrderBot (Wolex α) where
  bot_le s := by
    induction' s using Finset.Wolex.rec with s
    rw [le_def]
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    refine' Or.inr ⟨max' _ hs, _, by simp, max'_mem _ _⟩
    simp only [max'_lt_iff, ofWolex_bot, not_mem_empty, ofWolex_toWolex, false_iff]
    exact λ x hs hx ↦ lt_irrefl _ $ hs _ hx

/-- Wolex doesn't care if you remove the other set -/
@[simp]
lemma sdiff_le_sdiff_iff_le (s t : Finset α) :
    toWolex (s \ t) ≤ toWolex (t \ s) ↔ toWolex s ≤ toWolex t := by
  rw [le_iff_le_iff_lt_iff_lt, sdiff_lt_sdiff_iff_lt]

/-- If `s ⊂ t`, then `s` is less than `t` in the wolex order. Note the converse does not hold, as
`⊆` is not a linear order. -/
lemma wolex_lt_of_sSubset (h : s ⊂ t) : toWolex s < toWolex t := by
  rw [←sdiff_lt_sdiff_iff_lt, sdiff_eq_empty_iff_subset.2 h.1, toWolex_empty, bot_lt_iff_ne_bot, ←
    toWolex_empty, toWolex_ne_toWolex]
  simpa using h.not_subset

/-- If `s ⊆ t`, then `s ≤ t` in the wolex order. Note the converse does not hold, as `⊆` is not a
linear order. -/
lemma wolex_le_of_subset (h : s ⊆ t) : toWolex s ≤ toWolex t := by
  rw [←sdiff_le_sdiff_iff_le, sdiff_eq_empty_iff_subset.2 h, toWolex_empty]; exact bot_le

instance [Fintype α] : BoundedOrder (Wolex α) where
    top := toWolex univ
    le_top _x := wolex_le_of_subset (subset_univ _)

@[simp] lemma toWolex_univ [Fintype α] : toWolex (univ : Finset α) = ⊤ := rfl
@[simp] lemma ofWolex_top [Fintype α] : ofWolex (⊤ : Wolex α) = univ := rfl

/-- `s < {a}` in wolex iff all elements of `s` are strictly less than `a`. -/
lemma toWolex_lt_singleton : toWolex s < toWolex {a} ↔ ∀ x ∈ s, x < a := by
  simp only [toWolex_lt_toWolex, mem_singleton, ←and_assoc, exists_eq_right, ←not_le (a := a)]
  refine ⟨λ t x hx hax ↦ ?_, λ h ↦ ⟨λ z hz ↦ ?_, by simpa using h a⟩⟩
  · obtain hax | rfl := hax.lt_or_eq
    · exact hax.ne' $ (t.1 hax).1 hx
    · exact t.2 hx
  · exact ⟨fun i ↦ ((h _ i) hz.le).elim, fun i ↦ (hz.ne' i).elim⟩

/-- `{a} ≤ s` in wolex iff `r` contains an element greated than or equal to `a`. -/
lemma singleton_le_toWolex : (toWolex {a} : Wolex α) ≤ toWolex s ↔ ∃ x ∈ s, a ≤ x := by
  simp only [←not_lt, toWolex_lt_singleton, not_forall, exists_prop]

/-- Wolex is an extension of the base order. -/
lemma singleton_lt_singleton : (toWolex {a} : Wolex α) < toWolex {b} ↔ a < b := by
  simp [toWolex_lt_singleton]

/-- Wolex is an extension of the base order. -/
lemma singleton_le_singleton : (toWolex {a} : Wolex α) ≤ toWolex {b} ↔ a ≤ b := by
  rw [le_iff_le_iff_lt_iff_lt, singleton_lt_singleton]

/-- If `s` is before `t` in wolex, and everything in `t` is small, then everything in `s` is small.
-/
lemma forall_lt_mono (h₁ : toWolex s ≤ toWolex t) (h₂ : ∀ x ∈ t, x < a) : ∀ x ∈ s, x < a := by
  obtain rfl | ⟨k, z, -, hk⟩ := toWolex_le_toWolex.1 h₁
  · assumption
  · refine' λ x hx => lt_of_not_le fun h ↦ h.not_lt $ h₂ x _
    rwa [←z ((h₂ k hk).trans_le h)]

/-- Strictly monotone functions preserve the wolex ordering. -/
lemma toWolex_image_lt_toWolex_image (hf : StrictMono f) :
    toWolex (s.image f) < toWolex (t.image f) ↔ toWolex s < toWolex t := by
  simp only [toWolex_lt_toWolex, not_exists, mem_image, exists_prop, not_and]
  constructor
  · rintro ⟨k, z, q, k', _, rfl⟩
    exact ⟨k', λ x hx => by simpa [hf.injective.eq_iff] using z (hf hx),
      fun t ↦ q _ t rfl, ‹k' ∈ t›⟩
  rintro ⟨k, z, ka, _⟩
  refine' ⟨f k, λ x hx ↦ _, _, k, ‹k ∈ t›, rfl⟩
  · constructor
    all_goals
      rintro ⟨x', hx', rfl⟩
      refine' ⟨x', _, rfl⟩
      first
      | rwa [←z _]
      | rwa [z _]
      rwa [StrictMono.lt_iff_lt hf] at hx
  · simp only [hf.injective, Function.Injective.eq_iff]
    exact λ x hx ↦ ne_of_mem_of_not_mem hx ka

/-- Strictly monotone functions preserve the wolex ordering. -/
lemma toWolex_image_le_toWolex_image (hf : StrictMono f) :
    toWolex (s.image f) ≤ toWolex (t.image f) ↔ toWolex s ≤ toWolex t := by
  rw [le_iff_le_iff_lt_iff_lt, toWolex_image_lt_toWolex_image hf]

/-! ### Initial segments -/

/-- `𝒜` is an initial segment of the wolexigraphic order on sets of `r`, and that if `t` is below
`s` in wolex where `t` has size `r` and `s` is in `𝒜`, then `t` is also in `𝒜`. In effect, `𝒜` is
downwards closed with respect to wolex among sets of size `r`. -/
def IsInitSeg (𝒜 : Finset (Finset α)) (r : ℕ) : Prop :=
  (𝒜 : Set (Finset α)).Sized r ∧
    ∀ ⦃s t : Finset α⦄, s ∈ 𝒜 → toWolex t < toWolex s ∧ t.card = r → t ∈ 𝒜

@[simp] lemma isInitSeg_empty : IsInitSeg (∅ : Finset (Finset α)) r := by simp [IsInitSeg]

/-- Initial segments are nested in some way. In particular, if they're the same size they're equal.
-/
lemma IsInitSeg.total (h₁ : IsInitSeg 𝒜₁ r) (h₂ : IsInitSeg 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ := by
  classical
  simp_rw [←sdiff_eq_empty_iff_subset, ←not_nonempty_iff_eq_empty]
  by_contra' h
  obtain ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | rfl | hts := trichotomous_of (· < ·) (toWolex s) (toWolex t)
  · exact hs.2 $ h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · exact ht.2 hs.1
  · exact ht.2 $ h₁.2 hs.1 ⟨hts, h₂.1 ht.1⟩

variable [Fintype α]

/-- Gives all sets up to `s` with the same size as it: this is equivalent to
being an initial segment of wolex. -/
def initSeg (s : Finset α) : Finset (Finset α) :=
  univ.filter λ t ↦ s.card = t.card ∧ toWolex t ≤ toWolex s

@[simp]
lemma mem_initSeg : t ∈ initSeg s ↔ s.card = t.card ∧ toWolex t ≤ toWolex s := by simp [initSeg]

lemma mem_initSeg_self : s ∈ initSeg s := by simp
@[simp] lemma initSeg_nonempty : (initSeg s).Nonempty := ⟨s, mem_initSeg_self⟩

lemma isInitSeg_initSeg : IsInitSeg (initSeg s) s.card := by
  refine ⟨λ t ht => (mem_initSeg.1 ht).1.symm, λ t₁ t₂ ht₁ ht₂ ↦ mem_initSeg.2 ⟨ht₂.2.symm, ?_⟩⟩
  rw [mem_initSeg] at ht₁
  exact ht₂.1.le.trans ht₁.2

lemma IsInitSeg.exists_initSeg (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.Nonempty) :
    ∃ s : Finset α, s.card = r ∧ 𝒜 = initSeg s := by
  have hs := sup'_mem (ofWolex ⁻¹' 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toWolex
    (λ a ha ↦ by simpa using ha)
  refine' ⟨_, h𝒜.1 hs, _⟩
  ext t
  rw [mem_initSeg]
  refine' ⟨λ p ↦ _, _⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_lt
  · rwa [toWolex_inj.1 p]
  · exact h𝒜.2 hs ⟨p, cards ▸ h𝒜.1 hs⟩

/-- Being a nonempty initial segment of wolex if equivalent to being an `initSeg`. -/
lemma isInitSeg_iff_exists_initSeg :
    IsInitSeg 𝒜 r ∧ 𝒜.Nonempty ↔ ∃ s : Finset α, s.card = r ∧ 𝒜 = initSeg s := by
  refine ⟨λ h𝒜 ↦ h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩

end LinearOrder
end Wolex

open Wolex

/-!
### Wolex on `ℕ`

The wolexicographic order agrees with the order induced by interpreting a set of naturals as a
binary expansion.
-/

section Nat

/-- For subsets of ℕ, we can show that wolex is equivalent to binary. -/
lemma sum_two_pow_lt_iff_wolex_lt (s t : Finset ℕ) :
    ∑ i in s, 2 ^ i < ∑ i in t, 2 ^ i ↔ toWolex s < toWolex t := by
  have z : ∀ s t : Finset ℕ, toWolex s < toWolex t → ∑ i in s, 2 ^ i < ∑ i in t, 2 ^ i := by
    intro s t
    rw [←sdiff_lt_sdiff_iff_lt, toWolex_lt_toWolex]
    rintro ⟨a, ha, has, hat⟩
    rw [←sdiff_union_inter s t]
    conv_rhs => rw [←sdiff_union_inter t s]
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _), inter_comm,
      add_lt_add_iff_right]
    apply (@Nat.sum_two_pow_lt a (s \ t) _).trans_le
    · apply single_le_sum (λ _ _ ↦ Nat.zero_le _) hat
    intro x hx
    refine' (ne_of_mem_of_not_mem hx has).lt_or_lt.resolve_right $ λ hax ↦ _
    have := (ha hax).1 hx
    rw [mem_sdiff] at this hx
    exact hx.2 this.1
  refine' ⟨λ h ↦ (lt_trichotomy (toWolex s) $ toWolex t).resolve_right λ h₁ ↦
    h₁.elim _ (not_lt_of_gt h ∘ z _ _), z s t⟩
  rw [toWolex_inj]
  rintro rfl
  exact irrefl _ h

/-- For subsets of ℕ, we can show that wolex is equivalent to binary. -/
lemma sum_two_pow_le_iff_wolex_le (s t : Finset ℕ) :
    ∑ i in s, 2 ^ i ≤ ∑ i in t, 2 ^ i ↔ toWolex s ≤ toWolex t := by
  rw [le_iff_le_iff_lt_iff_lt, sum_two_pow_lt_iff_wolex_lt]

end Nat
end Finset
