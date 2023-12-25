/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import Nullstellensatz.Degree

#align_import nullstellensatz.degree_new

open Set Function Finsupp AddMonoidAlgebra

open scoped BigOperators Classical

universe u v

variable {α : Type v}

namespace MvPolynomial

variable {R σ : Type _}

-- this def is also given in flt-regular
def monomialDegree {s : Type _} (t : s →₀ ℕ) : ℕ :=
  t.Sum fun _ e => e

theorem Nat.term_le_sum {s : Finset α} (f : α → ℕ) {j : α} (hj : j ∈ s) : f j ≤ s.Sum f :=
  by
  revert j
  apply Finset.cons_induction_on s
  · simp
  · clear s
    intro x s hx hj j hc
    rw [Finset.sum_cons]
    simp only [Finset.mem_cons] at hc 
    cases' hc with j_eq_x j_in_s
    · simp [j_eq_x]
    · simp [(hj j_in_s).trans]

theorem le_monomialDegree {s : Type _} (t : s →₀ ℕ) (j : s) : t j ≤ monomialDegree t :=
  by
  by_cases c : j ∈ t.support
  · exact nat.term_le_sum _ c
  · simp only [Classical.not_not, Finsupp.mem_support_iff] at c 
    simp [c]

-- this holds for [ordered_add_comm_monoid N] if 0 ≤ n forall n ∈ N
theorem Finsupp.support_subset_of_le {s : Type _} {f g : s →₀ ℕ} (h : f ≤ g) :
    f.support ⊆ g.support :=
  by
  simp only [HasSubset.Subset, Finsupp.mem_support_iff, Ne.def]
  intro a ha
  by_contra c
  simpa [c] using lt_of_lt_of_le (Nat.pos_of_ne_zero ha) (h a)

-- this holds for [ordered_add_comm_monoid N] (with a different proof)
theorem Finsupp.sum_le_sum {s : Type _} {f g : s →₀ ℕ} (h : f ≤ g) :
    (f.Sum fun x y => y) ≤ g.Sum fun x y => y :=
  by
  rw [sum_of_support_subset f (finsupp.support_subset_of_le h) (fun x y => y) (by simp),
    Finsupp.sum]
  apply Finset.sum_le_sum
  intro i hi
  simp only [h i]

theorem monomialDegree_le_of_le {σ : Type _} {m m' : σ →₀ ℕ} (h : m' ≤ m) :
    monomialDegree m' ≤ monomialDegree m :=
  Finsupp.sum_le_sum h

theorem monomialDegree_add {σ : Type _} (m m' : σ →₀ ℕ) :
    monomialDegree (m + m') = monomialDegree m + monomialDegree m' :=
  sum_add_index (fun _ _ => rfl) fun _ _ _ _ => rfl

theorem monomialDegree_sub {σ : Type _} {m m' : σ →₀ ℕ} (h : m' ≤ m) :
    monomialDegree (m - m') = monomialDegree m - monomialDegree m' :=
  by
  rw [eq_tsub_iff_add_eq_of_le (monomial_degree_le_of_le h), ← monomial_degree_add]
  congr
  ext a
  rw [le_def] at h 
  simp only [Pi.add_apply, coe_tsub, coe_add, Pi.sub_apply, Nat.sub_add_cancel (h a)]

theorem nat_lemma_1 {a b c : ℕ} (h : c ≤ b) (h' : b - c ≤ a) : a - (b - c) = a + c - b :=
  by
  zify
  rw [Int.ofNat_sub]
  · rw [Int.ofNat_add, ← sub_add, sub_add_eq_add_sub]
  · apply tsub_le_iff_right.1 h'

theorem monomial_lemma_2 {σ : Type _} {m m' a : σ →₀ ℕ} (c : a - m ≤ m') : a ≤ m' + m :=
  tsub_le_iff_right.1 c

theorem monomial_lemma_3 {σ : Type _} {m m' : σ →₀ ℕ} : m ≤ m - m' + m' :=
  monomial_lemma_2 (le_refl _)

theorem monomial_lemma_1 {σ : Type _} {m m' a : σ →₀ ℕ} (h_m_le_a : m ≤ a) (c : a - m ≤ m') :
    m' - (a - m) = m' + m - a := by
  ext i
  simp only [Pi.add_apply, coe_tsub, coe_add, Pi.sub_apply]
  apply nat_lemma_1 (h_m_le_a i) (c i)

theorem monomialDegree_sub_le {σ : Type _} (m m' : σ →₀ ℕ) :
    monomialDegree m - monomialDegree m' ≤ monomialDegree (m - m') :=
  by
  simp only [tsub_le_iff_right, ← monomial_degree_add]
  apply monomial_degree_le_of_le
  apply monomial_lemma_3

theorem monomialDegree_zero_iff {σ : Type _} {m : σ →₀ ℕ} : monomialDegree m = 0 ↔ m = 0 :=
  by
  constructor
  · intro h
    ext i
    apply Nat.eq_zero_of_le_zero _
    apply (le_monomial_degree m i).trans
    rw [h]
  · intro h
    simp [h, monomial_degree]

-- This depends on flt-regular. Use total_degree_monomial once its merged into mathlib
theorem totalDegree_monomial_eq_monomialDegree {σ R : Type _} [CommSemiring R] {m : σ →₀ ℕ} {a : R}
    (h : a ≠ 0) : totalDegree (monomial m a) = monomialDegree m := by
  convert total_degree_monomial m h

-- Use monomial instead of single!
theorem monomialDegree_single {σ : Type _} {j : σ} {d : ℕ} : monomialDegree (single j d) = d := by
  simp [monomial_degree]

theorem eq_single_of_monomialDegree_eq {σ : Type _} (m : σ →₀ ℕ) (i : σ) :
    monomialDegree m = m i → m = single i (m i) :=
  by
  intro h
  rw [monomial_degree] at h 
  have h0 : single i (m i) ≤ m := by simp
  suffices y : ∀ j ∈ m.support, m j ≤ single i (m i) j
  · ext
    by_cases c : a ∈ m.support
    · exact le_antisymm (y a c) (h0 a)
    · by_cases c' : i = a
      · simp only [c', single_eq_same]
      · simpa [c', single_eq_of_ne, Ne.def, not_false_iff] using c
  by_contra c
  simp only [not_le, Classical.not_forall] at c 
  suffices x : (m.sum fun (_x : σ) (e : ℕ) => e) < m.support.sum ⇑m
  · simpa [Finsupp.sum] using x
  simpa only [h, ←
    sum_of_support_subset _ (finsupp.support_subset_of_le h0) (fun x y => y) (by simp),
    sum_single_index] using
    @Finset.sum_lt_sum σ ℕ _ (single i (m i)) m m.support (fun i h => h0 i) c

theorem monomialDegree_le_iff_eq_single {σ : Type _} (m : σ →₀ ℕ) (i : σ) :
    monomialDegree m ≤ m i ↔ m = single i (m i) :=
  by
  apply Iff.intro
  · intro h
    exact eq_single_of_monomial_degree_eq m i (le_antisymm (le_monomial_degree m i) h).symm
  · intro h
    rw [h]
    simp [monomial_degree_single]

theorem monomialDegree_le_totalDegree {σ R : Type _} [CommSemiring R] {m : σ →₀ ℕ}
    {f : MvPolynomial σ R} (h : m ∈ f.support) : monomialDegree m ≤ totalDegree f := by
  simp [total_degree, monomial_degree, Finset.le_sup h]

#print MvPolynomial.le_totalDegree /-
theorem le_totalDegree {R σ : Type _} [CommSemiring R] {i : σ} {p : MvPolynomial σ R} {m : σ →₀ ℕ}
    (h_m : m ∈ p.support) : m i ≤ p.totalDegree :=
  (le_monomialDegree m i).trans <| monomialDegree_le_totalDegree h_m
-/

theorem coeff_zero_of_degree_greater_than_totalDegree {R : Type _} [CommSemiring R] (t : σ →₀ ℕ)
    (f : MvPolynomial σ R) : monomialDegree t > totalDegree f → coeff t f = 0 :=
  by
  intro h
  by_cases c : t ∈ f.support
  · exfalso
    simpa using lt_of_le_of_lt (monomial_degree_le_total_degree c) h
  · simp only [Classical.not_not, mem_support_iff] at c 
    exact c

def MaxDegreeMonomial {R : Type _} [CommSemiring R] (t : σ →₀ ℕ) (f : MvPolynomial σ R) : Prop :=
  t ∈ f.support ∧ monomialDegree t = totalDegree f

-- this uses a lemma from flt-regular
theorem support_nonempty_iff {R σ : Type _} [CommSemiring R] {f : MvPolynomial σ R} :
    f.support.Nonempty ↔ f ≠ 0 := by
  rw [iff_not_comm]
  simp only [support_eq_empty, Finset.not_nonempty_iff_eq_empty]

-- see also flt-regular's exists_coeff_ne_zero_total_degree
theorem exists_maxDegreeMonomial {R : Type _} [CommSemiring R] {f : MvPolynomial σ R} (h : f ≠ 0) :
    ∃ t, MaxDegreeMonomial t f :=
  by
  simp only [max_degree_monomial, total_degree, monomial_degree]
  cases'
    Finset.exists_mem_eq_sup f.support (support_nonempty_iff.2 h) fun s : σ →₀ ℕ =>
      s.Sum fun (n : σ) (e : ℕ) => e with
    m hm
  exact ⟨m, ⟨hm.1, hm.2.symm⟩⟩

theorem eq_and_eq_of_le_add_le_eq {a1 a2 b1 b2 : ℕ} (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    (h : a1 + a2 = b1 + b2) : a1 = b1 ∧ a2 = b2 :=
  by
  apply And.intro
  · by_cases c : a1 < b1
    · simpa [h] using add_lt_add_of_lt_of_le c h2
    · exact le_antisymm h1 (not_lt.1 c)
  · by_cases c : a2 < b2
    · simpa [h] using add_lt_add_of_le_of_lt h1 c
    · exact le_antisymm h2 (not_lt.1 c)

theorem maxDegreeMonomial_hMul {σ R : Type _} [CommRing R] [IsDomain R] {f g : MvPolynomial σ R}
    {m : σ →₀ ℕ} (hf : f ≠ 0) (hg : g ≠ 0) (h : MaxDegreeMonomial m (f * g)) :
    ∃ mf mg, MaxDegreeMonomial mf f ∧ MaxDegreeMonomial mg g ∧ mf + mg = m :=
  by
  rw [max_degree_monomial] at h 
  rcases support_mul'' h.1 with ⟨mf, ⟨mg, h'⟩⟩
  use mf
  use mg
  suffices x : monomial_degree mf = f.total_degree ∧ monomial_degree mg = g.total_degree
  · exact ⟨⟨h'.1, x.1⟩, ⟨h'.2.1, x.2⟩, h'.2.2⟩
  apply
    eq_and_eq_of_le_add_le_eq (monomial_degree_le_total_degree h'.1)
      (monomial_degree_le_total_degree h'.2.1)
  simpa [h.2, h'.2.2, ← monomial_degree_add] using total_degree_mul' hf hg

def DominantMonomial {R : Type _} [CommSemiring R] (t : σ →₀ ℕ) (f : MvPolynomial σ R) : Prop :=
  MaxDegreeMonomial t f ∧ ∀ t' : σ →₀ ℕ, MaxDegreeMonomial t' f → t' = t

theorem dominantMonomial_of_factor_is_factor_of_maxDegreeMonomial {R : Type _} [CommRing R]
    [IsDomain R] (S : Finset R) (t t' : σ →₀ ℕ) (f g : MvPolynomial σ R)
    (hfg : MaxDegreeMonomial t (f * g)) (hf : f ≠ 0) (hg : DominantMonomial t' g) : t' ≤ t :=
  by
  by_cases c : g = 0
  · rw [c, dominant_monomial, max_degree_monomial] at hg 
    simpa using hg.1.1
  · rcases max_degree_monomial_mul hf c hfg with ⟨mf, ⟨mg, h⟩⟩
    rw [dominant_monomial] at hg 
    simp [← hg.2 mg h.2.1, ← h.2.2]

-- near total_degree_eq
theorem totalDegree_eq' {R σ : Type _} [CommSemiring R] (p : MvPolynomial σ R) :
    p.totalDegree = p.support.sup monomialDegree :=
  by
  rw [total_degree]
  congr; funext m

theorem totalDegree_lt_iff {R σ : Type _} [CommSemiring R] {f : MvPolynomial σ R} {d : ℕ}
    (h : 0 < d) : totalDegree f < d ↔ ∀ m : σ →₀ ℕ, m ∈ f.support → monomialDegree m < d := by
  rwa [total_degree_eq', Finset.sup_lt_iff]

theorem totalDegree_sub_lt {R σ : Type _} [CommRing R] [IsDomain R] {f g : MvPolynomial σ R} {k : ℕ}
    (h : 0 < k) (hf : ∀ m : σ →₀ ℕ, m ∈ f.support → k ≤ monomialDegree m → coeff m f = coeff m g)
    (hg : ∀ m : σ →₀ ℕ, m ∈ g.support → k ≤ monomialDegree m → coeff m f = coeff m g) :
    totalDegree (f - g) < k := by
  rw [total_degree_lt_iff h]
  intro m hm
  by_contra hc
  simp only [not_lt] at hc 
  have h' := support_sub σ f g hm
  simp only [mem_support_iff, Ne.def, coeff_sub, sub_eq_zero] at hm 
  simp [mem_union] at h' 
  cases' h' with cf cg
  · exact hm (hf m (by simpa using cf) hc)
  · exact hm (hg m (by simpa using cg) hc)

theorem maxDegreeMonomialIffOfEqDegree' {R σ : Type _} [CommSemiring R] (p : MvPolynomial σ R)
    {m m' : σ →₀ ℕ} (hm' : m' ∈ p.support) (h : monomialDegree m = monomialDegree m') :
    MaxDegreeMonomial m p → MaxDegreeMonomial m' p :=
  by
  intro h'
  constructor
  · exact hm'
  · rw [← h]
    exact h'.2

theorem maxDegreeMonomial_iff_of_eq_degree {R σ : Type _} [CommSemiring R] (p : MvPolynomial σ R)
    {m m' : σ →₀ ℕ} (hm : m ∈ p.support) (hm' : m' ∈ p.support)
    (h : monomialDegree m = monomialDegree m') : MaxDegreeMonomial m p ↔ MaxDegreeMonomial m' p :=
  by
  constructor
  · apply max_degree_monomial_iff_of_eq_degree'
    · exact hm'
    · exact h
  · apply max_degree_monomial_iff_of_eq_degree'
    · exact hm
    · exact h.symm

theorem maxDegreeMonomial_iff {R σ : Type _} [CommRing R] {f : MvPolynomial σ R} {m : σ →₀ ℕ} :
    MaxDegreeMonomial m f ↔
      m ∈ f.support ∧ ∀ m' ∈ f.support, monomialDegree m' ≤ monomialDegree m :=
  by
  constructor
  · intro h
    constructor
    · exact h.1
    · intro m' hm'
      have t := h.2
      rw [total_degree_eq'] at t 
      rw [t]
      apply Finset.le_sup hm'
  · intro h
    constructor
    · exact h.1
    · rw [total_degree_eq']
      rw [← Finset.sup'_eq_sup]
      · apply le_antisymm
        · apply Finset.le_sup'
          exact h.1
        · apply Finset.sup'_le
          exact h.2

theorem dominantMonomial_iff {R σ : Type _} [CommRing R] {f : MvPolynomial σ R} {m : σ →₀ ℕ} :
    DominantMonomial m f →
      ∀ m' ∈ f.support,
        monomialDegree m' ≤ monomialDegree m ∧ (monomialDegree m' = monomialDegree m → m' = m) :=
  by
  intro h m' hm'
  constructor
  · apply (max_degree_monomial_iff.1 h.1).2
    exact hm'
  · intro h1
    apply h.2
    rw [max_degree_monomial_iff_of_eq_degree f hm' h.1.1 h1]
    exact h.1

theorem induction_on_totalDegree {R σ : Type _} [CommSemiring R] {M : MvPolynomial σ R → Prop}
    (p : MvPolynomial σ R)
    (h : ∀ p' : MvPolynomial σ R, (∀ q, totalDegree q < totalDegree p' → M q) → M p') : M p :=
  by
  let P : ℕ → Prop := fun n => ∀ p : MvPolynomial σ R, total_degree p ≤ n → M p
  suffices l' : ∀ n, P n
  · apply l' (total_degree p)
    rfl
  · intro n
    induction' n with d hd
    · intro p hp
      apply h p
      intro q hq
      simpa using lt_of_lt_of_le hq hp
    · intro p hp
      apply h p
      intro q hq
      exact hd q (Nat.le_of_lt_succ (lt_of_lt_of_le hq hp))

theorem induction_on_new {R σ : Type _} [CommSemiring R] {M : MvPolynomial σ R → Prop}
    (p : MvPolynomial σ R)
    (h_add_weak :
      ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R),
        a ∉ f.support → b ≠ 0 → M f → M (monomial a b) → M (monomial a b + f))
    (h_monomial :
      ∀ m : σ →₀ ℕ,
        ∀ b : R,
          (∀ p : MvPolynomial σ R, totalDegree p < monomialDegree m → M p) → M (monomial m b)) :
    M p := by
  apply induction_on_total_degree
  · intro p
    apply induction_on''' p
    · intro a h
      apply h_monomial
      intro x h2
      simpa [monomial_degree] using h2
    · intro a b f ha hb hMf h
      apply h_add_weak a b f ha hb (hMf _)
      · apply h_monomial
        intro p' hp'
        suffices h' : p'.total_degree < (monomial a b).totalDegree
        · apply h p' ∘ lt_of_lt_of_le h'
          rw [total_degree_add_eq_of_disjoint_support]
          · simp only [le_refl, true_or_iff, le_max_iff]
          ·
            simpa only [support_monomial, hb, Classical.not_not, mem_support_iff, if_false,
              Finset.disjoint_singleton_left, Classical.not_not, Finsupp.mem_support_iff] using ha
        rw [total_degree_monomial_eq_monomial_degree]
        · exact hp'
        · exact hb
      · intro q hq
        apply h q ∘ lt_of_lt_of_le hq
        rw [total_degree_add_eq_of_disjoint_support]
        · simp only [le_refl, or_true_iff, le_max_iff]
        ·
          simpa only [support_monomial, hb, Classical.not_not, mem_support_iff, if_false,
            Finset.disjoint_singleton_left, Classical.not_not, Finsupp.mem_support_iff] using ha

end MvPolynomial

