import Mathlib
import LeanCamCombi.Mathlib.Data.Prod.Lex
import LeanCamCombi.GrowthInGroups.ChevalleyPrelim
import LeanCamCombi.GrowthInGroups.ConstructiblePrimeSpectrum
import LeanCamCombi.Mathlib.Algebra.Order.GroupWithZero.Unbundled
import LeanCamCombi.Mathlib.Algebra.Module.Submodule.Pointwise

variable {R M A} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

open Polynomial TensorProduct PrimeSpectrum

@[ext]
structure InductionObj (R) [CommRing R] (n : ℕ) where
  val : Fin n → R[X]

variable {n : ℕ} (S T : InductionObj R n)

instance : CoeFun (InductionObj R n) (fun _ ↦ Fin n → R[X]) := ⟨InductionObj.val⟩

namespace InductionObj

def coeffSubmodule : Submodule ℤ R :=
  Submodule.span ℤ ({1} ∪ ⋃ i, Set.range (S.val i).coeff)

lemma one_le_coeffSubmodule : 1 ≤ S.coeffSubmodule := by
  rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.subset_span (.inl rfl)

variable (n) in
abbrev DegreeType := (Fin n → WithBot ℕ) ×ₗ Prop

def degree : DegreeType n :=
  toLex (Polynomial.degree ∘ S.val, ¬ ∃ i, (S.val i).Monic ∧
    ∀ j, S.val j ≠ 0 → (S.val i).degree ≤ (S.val j).degree)

@[simp] lemma ofLex_degree_fst (i) : (ofLex S.degree).fst i = (S.val i).degree := rfl
lemma ofLex_degree_snd : (ofLex S.degree).snd = ¬ ∃ i, (S.val i).Monic ∧
    ∀ j, S.val j ≠ 0 → (S.val i).degree ≤ (S.val j).degree := rfl

def degBound : ℕ := 2 ^ ∑ i, (S.val i).natDegree

def exponentBound : ℕ := S.degBound ^ S.degBound

def InductionStatement (R) (n) [CommRing R] (S : InductionObj R n) : Prop :=
  ∀ f, ∃ T : Finset (Σ n, R × (Fin n → R)),
    comap C '' (zeroLocus (Set.range S.val) \ zeroLocus {f}) =
      ⋃ C ∈ T, (zeroLocus (Set.range C.2.2) \ zeroLocus {C.2.1}) ∧
    ∀ C ∈ T, C.1 ≤ S.degBound ∧ ∀ i, C.2.2 i ∈ S.coeffSubmodule ^ S.exponentBound

universe u

-- lemma Ideal.span_range_update_divByMonic {ι : Type*} [DecidableEq ι]
--     (v : ι → R[X]) (i j : ι) (hij : i ≠ j) (h : IsUnit (v i).leadingCoeff) :
--     Ideal.span (Set.range (Function.update v j (v j %ₘ (C ((h.unit⁻¹ : Rˣ) : R) * v i)))) =
--       Ideal.span (Set.range v) := by
--   have H : (C ((h.unit⁻¹ : Rˣ) : R) * v i).Monic :=
--     Polynomial.monic_unit_leadingCoeff_inv_smul (v i) h
--   refine le_antisymm ?_ ?_ <;>
--     simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe]
--   · intro k
--     by_cases hjk : j = k
--     · subst hjk
--       rw [Function.update_same, modByMonic_eq_sub_mul_div (v j) H]
--       apply sub_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _
--         (Ideal.mul_mem_left _ _ <| Ideal.subset_span ?_))
--       · exact ⟨j, rfl⟩
--       · exact ⟨i, rfl⟩
--     exact Ideal.subset_span ⟨k, (Function.update_noteq (.symm hjk) _ _).symm⟩
--   · intro k
--     by_cases hjk : j = k
--     · subst hjk
--       nth_rw 2 [← modByMonic_add_div (v j) H]
--       apply add_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _
--         (Ideal.mul_mem_left _ _ <| Ideal.subset_span ?_))
--       · exact ⟨j, Function.update_same _ _ _⟩
--       · exact ⟨i, Function.update_noteq hij _ _⟩
--     exact Ideal.subset_span ⟨k, Function.update_noteq (.symm hjk) _ _⟩

lemma Prod.Lex.lt_iff'' {α β} [PartialOrder α] [Preorder β] (a b : α ×ₗ β) :
    a < b ↔ (ofLex a).1 ≤ (ofLex b).1 ∧
      ((ofLex a).1 = (ofLex b).1 → (ofLex a).2 < (ofLex b).2) := by
  show toLex (ofLex a) < toLex (ofLex b) ↔ _
  rw [Prod.Lex.lt_iff]
  simp only [lt_iff_le_not_le, le_antisymm_iff]
  tauto

lemma foo_induction (n : ℕ)
    (P : ∀ (R : Type u) [CommRing R], (InductionObj R n) → Prop)
    (hP₀ : ∀ (R) [CommRing R] (e : InductionObj R n) (i : Fin n),
      (e.1 i).Monic → (∀ j ≠ i, e.1 j = 0) → P R e)
    (hP₁ : ∀ (R) [CommRing R], P R ⟨0⟩)
    (hP₃ : ∀ (R) [CommRing R] (e : InductionObj R n) (i j : Fin n),
      (e.1 i).Monic → (e.1 i).degree ≤ (e.1 j).degree → i ≠ j →
      P R ⟨Function.update e.1 j (e.1 j %ₘ e.1 i)⟩ → P R e)
    (hP : ∀ (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n)
      (hi : c = (e.1 i).leadingCoeff),
      P (Localization.Away c) ⟨C (IsLocalization.Away.invSelf (S := Localization.Away c) c) •
        mapRingHom (algebraMap _ _) ∘ e.val⟩ →
      P (R ⧸ Ideal.span {c}) ⟨mapRingHom (algebraMap _ _) ∘ e.val⟩ → P R e)
    {R} [CommRing R] (e : InductionObj R n) : P R e := by
  classical
  set v := e.degree with hv
  clear_value v
  induction v using wellFounded_lt (α := InductionObj.DegreeType n).induction generalizing R with
  | h v H_IH =>
    by_cases he0 : e = ⟨0⟩
    · exact he0 ▸ hP₁ R
    cases subsingleton_or_nontrivial R
    · convert hP₁ R; ext; exact Subsingleton.elim _ _
    simp only [InductionObj.ext_iff, funext_iff, Pi.zero_apply, not_forall] at he0
    -- Case I : The `e i ≠ 0` with minimal degree has invertible leading coefficient
    by_cases H : (∃ i, (e.1 i).Monic ∧ ∀ j, e.1 j ≠ 0 → (e.1 i).degree ≤ (e.1 j).degree)
    · obtain ⟨i, hi, i_min⟩ := H
      -- Case I.ii : `e j = 0` for all `j ≠ i`.
      by_cases H' : ∀ j ≠ i, e.1 j = 0
      -- then `I = Ideal.span {e i}`
      · exact hP₀ R e i hi H'
      -- Case I.i : There is another `e j ≠ 0`
      · simp only [ne_eq, not_forall, Classical.not_imp] at H'
        obtain ⟨j, hj, hj'⟩ := H'
        replace i_min := i_min j hj'
        -- then we can replace `e j` with `e j %ₘ (C h.unit⁻¹ * e i) `
        -- with `h : IsUnit (e i).leadingCoeff`.
        apply hP₃ R e i j hi i_min (.symm hj) (H_IH _ ?_ _ rfl)
        refine .left _ _ (lt_of_le_of_ne (b := (ofLex v).1) ?_ ?_)
        · intro k
          simp only [Function.comp_apply, Function.update_apply, hv, ne_eq, not_exists, not_and,
            not_forall, Classical.not_imp, not_le, ofLex_toLex]
          split_ifs with hjk
          · rw [hjk]
            exact (degree_modByMonic_le _ hi).trans i_min
          · exact le_rfl
        · simp only [hv, ne_eq, not_exists, not_and, not_forall, not_le, funext_iff,
            Function.comp_apply, exists_prop, ofLex_toLex]
          use j
          simp only [Function.update_same]
          refine ((degree_modByMonic_lt _ hi).trans_le i_min).ne
    -- Case II : The `e i ≠ 0` with minimal degree has non-invertible leading coefficient
    obtain ⟨i, hi, i_min⟩ : ∃ i, e.1 i ≠ 0 ∧ ∀ j, e.1 j ≠ 0 → (e.1 i).degree ≤ (e.1 j).degree := by
      have : ∃ n : ℕ, ∃ i, (e.1 i).degree = n ∧ (e.1 i) ≠ 0 := by
        obtain ⟨i, hi⟩ := he0; exact ⟨(e.1 i).natDegree, i, degree_eq_natDegree hi, hi⟩
      let m := Nat.find this
      obtain ⟨i, hi, hi'⟩ : ∃ i, (e.1 i).degree = m ∧ (e.1 i) ≠ 0 := Nat.find_spec this
      refine ⟨i, hi', fun j hj ↦ ?_⟩
      refine hi.le.trans ?_
      rw [degree_eq_natDegree hj, Nat.cast_le]
      exact Nat.find_min' _ ⟨j, degree_eq_natDegree hj, hj⟩
    have : ¬ (e.1 i).Monic := fun HH ↦ H ⟨i, HH, i_min⟩
    -- We replace `R` by `R ⧸ Ideal.span {(e i).leadingCoeff}` where `(e i).degree` is lowered
    -- and `Localization.Away (e i).leadingCoeff` where `(e i).leadingCoeff` becomes invertible.
    apply hP _ _ i e rfl (H_IH _ ?_ _ rfl) (H_IH _ ?_ _ rfl)
    · rw [hv, Prod.Lex.lt_iff'']
      constructor
      · intro j
        simp only [coe_mapRingHom, InductionObj.ofLex_degree_fst, Pi.smul_apply,
          Function.comp_apply, smul_eq_mul]
        refine ((degree_mul_le _ _).trans (add_le_add degree_C_le (degree_map_le _ _))).trans ?_
        simp
      rw [lt_iff_le_not_le]
      simp only [coe_mapRingHom, funext_iff, InductionObj.ofLex_degree_fst, Pi.smul_apply,
        Function.comp_apply, smul_eq_mul, show (ofLex e.degree).2 from H,
        le_Prop_eq, implies_true, true_implies, true_and]
      simp only [InductionObj.ofLex_degree_snd, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        ne_eq, not_exists, not_and, not_forall, Classical.not_imp, not_le, not_lt]
      intro h_eq
      refine ⟨i, ?_, ?_⟩
      · rw [Monic.def, ← coeff_natDegree (p := _ * _), natDegree_eq_of_degree_eq (h_eq i),
          coeff_C_mul, coeff_map, coeff_natDegree, mul_comm, IsLocalization.Away.mul_invSelf]
      · intro j hj; rw [h_eq, h_eq]; exact i_min j fun H ↦ (by simp [H] at hj)
    · rw [hv]
      refine .left _ _ (lt_of_le_of_ne ?_ ?_)
      · intro j; simpa using degree_map_le _ _
      simp only [coe_mapRingHom, Function.comp_apply, ne_eq, hv, ofLex_toLex,
        not_exists, not_and, not_forall, Classical.not_imp, not_le, H, not_false_eq_true]
      intro h_eq
      replace h_eq := congr_fun h_eq i
      simp only [Ideal.Quotient.algebraMap_eq, Function.comp_apply, degree_map_eq_iff,
        Ideal.Quotient.mk_singleton_self, ne_eq, not_true_eq_false, false_or] at h_eq
      exact hi h_eq

universe v

lemma RingHom.FinitePresentation.polynomial_induction
    (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S], (R →+* S) → Prop)
    (Q : ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S], (R →+* S) → Prop)
    (h₁ : ∀ (R) [CommRing R], P R R[X] C)
    (h₂ : ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] (f : R →+* S),
      Function.Surjective f → (RingHom.ker f).FG → Q R S f)
    (h₃ : ∀ (R) [CommRing R] (S) [CommRing S] (T) [CommRing T] (f : R →+* S) (g : S →+* T),
      P R S f → Q S T g → Q R T (g.comp f))
    {R S} [CommRing R] [CommRing S] (f : R →+* S) (hf : RingHom.FinitePresentation f) :
    Q R S f := by
  obtain ⟨n, g, hg, hg'⟩ := hf
  let g' := letI := f.toAlgebra; g.toRingHom
  replace hg : Function.Surjective g' := hg
  replace hg' : (RingHom.ker g').FG := hg'
  have : g'.comp (MvPolynomial.C) = f := letI := f.toAlgebra; g.comp_algebraMap
  clear_value g'
  subst this
  clear g
  induction n generalizing R S with
  | zero =>
    refine h₂ _ _ _ (hg.comp (MvPolynomial.C_surjective (Fin 0))) ?_
    rw [← RingHom.comap_ker]
    convert hg'.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom using 1
    simp only [RingEquiv.toRingHom_eq_coe]
    exact Ideal.comap_symm (RingHom.ker g') (MvPolynomial.isEmptyRingEquiv R (Fin 0))
  | succ n IH =>
    let e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin n) R[X] :=
      (MvPolynomial.renameEquiv R (_root_.finSuccEquiv n)).trans
        (MvPolynomial.optionEquivRight R (Fin n))
    have he : (RingHom.ker (g'.comp <| RingHomClass.toRingHom e.symm)).FG := by
      rw [← RingHom.comap_ker]
      convert hg'.map e.toAlgHom.toRingHom using 1
      exact Ideal.comap_symm (RingHom.ker g') e.toRingEquiv
    have := IH (R := R[X]) (S := S) (g'.comp e.symm) (hg.comp e.symm.surjective) he
    convert h₃ _ _ _ _ _ (h₁ _) this using 1
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    congr 1
    ext : 1
    simp [e]

lemma Polynomial.ker_mapRingHom' {R S} [CommRing R] [CommRing S] (f : R →+* S) :
    RingHom.ker (mapRingHom f) = (RingHom.ker f).map C := by
  rw [← Polynomial.ker_mapRingHom]
  rfl

lemma mapRingHom_comp_C {R S} [CommRing R] [CommRing S] (f : R →+* S) :
    (mapRingHom f).comp C = C.comp f := by ext; simp

lemma Polynomial.isLocalization {R} [CommRing R] (S : Submonoid R) (A) [CommRing A] [Algebra R A]
    [IsLocalization S A] :
    letI := (mapRingHom (algebraMap R A)).toAlgebra; IsLocalization (S.map C) A[X] := by
  letI := (mapRingHom (algebraMap R A)).toAlgebra
  constructor
  · rintro ⟨_, r, hr, rfl⟩
    simpa [RingHom.algebraMap_toAlgebra] using (IsLocalization.map_units A ⟨r, hr⟩).map C
  · intro z
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec S z
    refine ⟨⟨IsLocalization.integerNormalization S z, _, b, b.2, rfl⟩, ?_⟩
    ext i
    simp only [RingHom.algebraMap_toAlgebra, coe_mapRingHom, map_C, coeff_mul_C, coeff_map, hb,
      mul_comm, Algebra.smul_def]
  · intros x y e
    rw [← sub_eq_zero, ← map_sub, RingHom.algebraMap_toAlgebra, ← RingHom.mem_ker,
      Polynomial.ker_mapRingHom', Ideal.mem_map_C_iff] at e
    simp only [coeff_sub, RingHom.mem_ker, map_sub, sub_eq_zero,
      IsLocalization.eq_iff_exists S] at e
    choose c hc using e
    refine ⟨⟨_, _, ((x.support ∪ y.support).prod c).2, rfl⟩, ?_⟩
    ext i
    simp only [coeff_C_mul]
    by_cases hi : i ∈ x.support ∪ y.support
    · obtain ⟨k, e⟩ := Finset.dvd_prod_of_mem c hi
      simp only [e, mul_comm _ k, Submonoid.coe_mul _ k, mul_assoc, hc]
    · simp only [Finset.mem_union, mem_support_iff, ne_eq, not_or, not_not] at hi
      simp [hi.1, hi.2]

lemma comap_C_eq_comap_quotient_union_comap_localization (s : Set (PrimeSpectrum R[X])) (c : R) :
    comap C '' s =
      comap (Ideal.Quotient.mk (.span {c})) '' (comap C ''
        (comap (mapRingHom (Ideal.Quotient.mk _)) ⁻¹' s)) ∪
      comap (algebraMap R (Localization.Away c)) '' (comap C ''
        (comap (mapRingHom (algebraMap R (Localization.Away c))) ⁻¹' s)) := by
  simp_rw [← Set.image_comp, ← ContinuousMap.coe_comp, ← comap_comp, ← mapRingHom_comp_C,
    comap_comp, ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range,
    ← Set.image_union, ← Set.inter_union_distrib_left]
  letI := (mapRingHom (algebraMap R (Localization.Away c))).toAlgebra
  suffices Set.range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) =
      (Set.range (comap (algebraMap R[X] (Localization.Away c)[X])))ᶜ by
    rw [this, RingHom.algebraMap_toAlgebra, Set.compl_union_self, Set.inter_univ]
  have := Polynomial.isLocalization (.powers c) (Localization.Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj, localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom', Ideal.map_span]

local notation "°" => Polynomial.natDegree

local notation "↝" => Polynomial.leadingCoeff

local notation3 "coeff("p")" => Set.range (Polynomial.coeff p)

-- lemma span_range_coeff_mul :

open Submodule Set Polynomial in
lemma divModByMonicAux_mem_span_coeff_pow : ∀ (p q : R[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i ∈
      span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (p.natDegree)
    ∧
    (p.divModByMonicAux hq).2.coeff i ∈
      span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (p.natDegree)
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i ∈ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (° p) := by
      have H : span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ≤
          span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (° p) := by
        apply le_self_pow₀
        · rw [one_eq_span, span_le, Set.singleton_subset_iff]
          exact subset_span (.inl rfl)
        · positivity
      apply H
      exact subset_span (.inr (.inl ⟨i, rfl⟩))
    split_ifs with hpq
    · simp only [coeff_add, coeff_C_mul, coeff_X_pow]
      generalize hr : (p - q * (C (↝ p) * X ^ (° p - ° q))) = r
      by_cases hr' : r = 0
      · simp only [mul_ite, mul_one, mul_zero, hr', divModByMonicAux, degree_zero,
          le_bot_iff, degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte,
          Prod.mk_zero_zero, Prod.fst_zero, coeff_zero, add_zero, Prod.snd_zero, Submodule.zero_mem,
          and_true]
        split_ifs
        · exact H₀ _
        · exact zero_mem _
      have H : span ℤ coeff(r) ≤ span ℤ coeff(p) ⊔ span ℤ coeff(p) * span ℤ coeff(q) := by
        rw [span_le, ← hr]
        rintro _ ⟨i, rfl⟩
        rw [coeff_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
        apply sub_mem
        · refine SetLike.le_def.mp le_sup_left ?_
          exact subset_span ⟨i, rfl⟩
        · split_ifs
          · rw [mul_comm]
            refine SetLike.le_def.mp le_sup_right (mul_mem_mul ?_ ?_)
            · exact subset_span ⟨_, rfl⟩
            · exact subset_span ⟨_, rfl⟩
          · exact zero_mem _
      have H' : ° r < ° p :=
        natDegree_lt_natDegree hr' (hr ▸ div_wf_lemma hpq hq)
      have H'' : span ℤ ({1} ∪ (coeff(r) ∪ coeff(q))) ^ 2 ^ (° r) ≤
          span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (° p) :=
        calc span ℤ ({1} ∪ (coeff(r) ∪ coeff(q))) ^ 2 ^ (° r)
          _ = (span ℤ {1} ⊔ span ℤ coeff(r) ⊔ span ℤ coeff(q)) ^ 2 ^ (° r) := by
              simp_rw [span_union, sup_assoc]
          _ ≤ (span ℤ {1} ⊔ (span ℤ coeff(p) ⊔ span ℤ coeff(p) * span ℤ coeff(q)) ⊔ span ℤ coeff(q)) ^ 2 ^ (° r) := by gcongr
          _ ≤ ((span ℤ {1} ⊔ span ℤ coeff(p) ⊔ span ℤ coeff(q)) ^ 2) ^ 2 ^ (° r) := by
              gcongr
              rw [pow_two]
              simp only [Submodule.mul_sup, Submodule.sup_mul, ← Submodule.one_eq_span,
                one_mul, mul_one, sup_le_iff]
              refine ⟨⟨by simp only [sup_assoc, le_sup_left], ?_, ?_⟩, ?_⟩
              · apply le_sup_of_le_left
                apply le_sup_of_le_left
                apply le_sup_of_le_left
                exact le_sup_right
              · apply le_sup_of_le_right
                apply le_sup_of_le_left
                exact le_sup_right
              · apply le_sup_of_le_left
                apply le_sup_of_le_left
                exact le_sup_right
          _ = (span ℤ {1} ⊔ span ℤ coeff(p) ⊔ span ℤ coeff(q)) ^ 2 ^ (1 + ° r) := by
              rw [← pow_mul, pow_add 2 1, pow_one]
          _ = span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (1 + ° r) := by
              simp_rw [span_union, sup_assoc]
          _ ≤ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (° p) := by
              gcongr
              · rw [one_eq_span]
                apply span_mono
                exact Set.subset_union_left
              · exact Nat.le_succ 1
              · exact Nat.one_add_le_iff.mpr H'
      constructor
      · apply add_mem
        · split_ifs <;> simp only [mul_one, mul_zero]
          · exact H₀ _
          · exact zero_mem _
        · exact H'' (divModByMonicAux_mem_span_coeff_pow r _ hq i).1
      · exact H'' (divModByMonicAux_mem_span_coeff_pow _ _ hq i).2
    · constructor
      · simp
      · exact H₀ _
  termination_by p => ° p

open Submodule Set Polynomial in
lemma modByMonic_mem_span_coeff_pow (p q : R[X]) (i) :
    (p %ₘ q).coeff i ∈ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ p.natDegree := by
  delta modByMonic
  split_ifs with H
  · exact (divModByMonicAux_mem_span_coeff_pow p q H i).2
  · have H : span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ≤
        span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (° p) := by
      apply le_self_pow₀
      · rw [one_eq_span, span_le, Set.singleton_subset_iff]
        exact subset_span (.inl rfl)
      · positivity
    apply H
    exact subset_span (.inr (.inl ⟨i, rfl⟩))

lemma Ideal.span_range_update_divByMonic {ι : Type*} [DecidableEq ι]
    (v : ι → R[X]) (i j : ι) (hij : i ≠ j) (H : (v i).Monic) :
    Ideal.span (Set.range (Function.update v j (v j %ₘ v i))) =
      Ideal.span (Set.range v) := by
  refine le_antisymm ?_ ?_ <;>
    simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe]
  · intro k
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_same, modByMonic_eq_sub_mul_div (v j) H]
      apply sub_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
      · exact ⟨j, rfl⟩
      · exact ⟨i, rfl⟩
    exact Ideal.subset_span ⟨k, (Function.update_noteq (.symm hjk) _ _).symm⟩
  · intro k
    by_cases hjk : j = k
    · subst hjk
      nth_rw 2 [← modByMonic_add_div (v j) H]
      apply add_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
      · exact ⟨j, Function.update_same _ _ _⟩
      · exact ⟨i, Function.update_noteq hij _ _⟩
    exact Ideal.subset_span ⟨k, Function.update_noteq (.symm hjk) _ _⟩

lemma induction_aux (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n)
      (hi : c = (e.1 i).leadingCoeff) :
      InductionStatement (Localization.Away c) n
        ⟨C (IsLocalization.Away.invSelf (S := Localization.Away c) c) •
          mapRingHom (algebraMap _ _) ∘ e.val⟩ →
      InductionStatement (R ⧸ Ideal.span {c}) n ⟨mapRingHom (algebraMap _ _) ∘ e.val⟩ →
        InductionStatement R n e := by
  intro H₁ H₂ f
  obtain ⟨T₁, hT₁, HT₁⟩ := H₁ (mapRingHom (algebraMap _ _) f)
  obtain ⟨T₂, hT₂, HT₂⟩ := H₂ (mapRingHom (algebraMap _ _) f)
  simp only [coe_mapRingHom] at HT₁
  sorry


lemma isConstructible_comap_C_zeroLocus_sdiff_zeroLocus {R} [CommRing R] {n}
    (S : InductionObj R n) : InductionStatement R n S := by
  classical
  revert S
  apply foo_induction
  · intros R _ g i hi hi_min f; sorry
    -- let M := R[X] ⧸ Ideal.span {g.1 i}
    -- have : Module.Free R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    -- have : Module.Finite R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    -- refine ⟨(Finset.range (Module.finrank R M)).image
    --   fun j ↦ ⟨0, (Algebra.lmul R M (Ideal.Quotient.mk _ f)).charpoly.coeff j, 0⟩, ?_, ?_⟩
    -- · ext x
    --   have : zeroLocus (Set.range g.val) = zeroLocus {g.1 i} := by
    --     rw [Set.range_eq_iUnion, zeroLocus_iUnion]
    --     refine (Set.iInter_subset _ _).antisymm (Set.subset_iInter fun j ↦ ?_)
    --     by_cases hij : i = j
    --     · subst hij; rfl
    --     · rw [hi_min j (.symm hij), zeroLocus_singleton_zero]; exact Set.subset_univ _
    --   rw [this, ← Polynomial.algebraMap_eq, mem_image_comap_zeroLocus_sdiff,
    --     IsScalarTower.algebraMap_apply R[X] M, isNilpotent_tensor_residueField_iff]
    --   simp [Set.subset_def, M]
    -- · simp
  · intro R _ f; sorry
    -- refine ⟨(Finset.range (f.natDegree + 2)).image fun j ↦ ⟨0, f.coeff j, 0⟩, ?_, ?_⟩
    -- · convert image_comap_C_basicOpen f
    --   · simp only [basicOpen_eq_zeroLocus_compl, Set.compl_eq_univ_diff]
    --     congr 1
    --     rw [← Set.univ_subset_iff]
    --     rintro x _ _ ⟨_, rfl⟩
    --     exact zero_mem x.asIdeal
    --   · suffices Set.range f.coeff = ⋃ i < f.natDegree + 2, {f.coeff i} by
    --       simp [← Set.compl_eq_univ_diff, eq_compl_comm (y := zeroLocus _),
    --         ← zeroLocus_iUnion₂, this]
    --     trans f.coeff '' (Set.Iio (f.natDegree + 2))
    --     · refine ((Set.image_subset_range _ _).antisymm ?_).symm
    --       rintro _ ⟨i, rfl⟩
    --       by_cases hi : i ≤ f.natDegree
    --       · exact ⟨i, hi.trans_lt (by simp), rfl⟩
    --       · exact ⟨f.natDegree + 1, by simp,
    --           by simp [f.coeff_eq_zero_of_natDegree_lt (lt_of_not_le hi)]⟩
    --     · ext; simp [eq_comm]
    -- · simp
  · intro R _ c i j hi hle hne H f
    obtain ⟨S, hS, hS'⟩ := H f
    refine ⟨S, Eq.trans ?_ hS, ?_⟩
    · rw [← zeroLocus_span (Set.range _), ← zeroLocus_span (Set.range _),
        Ideal.span_range_update_divByMonic _ _ _ hne hi]
    · intro C hC; sorry
      -- let c' : InductionObj _ _ := ⟨Function.update c.val j (c.val j %ₘ c.val i)⟩
      -- have deg_bound₁ : c'.degBound ≤ c.degBound := by
      --   dsimp [InductionObj.degBound]
      --   gcongr with k
      --   · exact Nat.le_succ _
      --   · rw [Function.update_apply]
      --     split_ifs with hkj
      --     · subst hkj; exact (natDegree_modByMonic_le _ hi).trans (natDegree_le_natDegree hle)
      --     · rfl
      -- refine ⟨(hS' C hC).1.trans deg_bound₁, fun k ↦ SetLike.le_def.mp ?_ ((hS' C hC).2 k)⟩
      -- show c'.coeffSubmodule ^ c'.exponentBound ≤ _
      -- delta exponentBound
      -- suffices hij : c'.coeffSubmodule ≤ c.coeffSubmodule ^ (2 ^ (c.val j).natDegree) by
      --   by_cases hi' : c.val i = 1
      --   · gcongr
      --     · exact c.one_le_coeffSubmodule
      --     · refine Submodule.span_le.mpr (Set.union_subset ?_ ?_)
      --       · exact Set.subset_union_left.trans Submodule.subset_span
      --       · refine Set.iUnion_subset fun k ↦ ?_
      --         simp only [Function.update_apply, hi', modByMonic_one]
      --         split_ifs
      --         · rintro _ ⟨_, rfl⟩
      --           exact zero_mem _
      --         · exact (Set.subset_iUnion (fun i ↦ coeff(c.val i)) k).trans
      --             (Set.subset_union_right.trans Submodule.subset_span)
      --     refine (pow_le_pow_left' deg_bound₁ _).trans (pow_le_pow_right' ?_ deg_bound₁)
      --     rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, InductionObj.degBound]
      --     positivity
      --   refine (pow_le_pow_left' hij _).trans ?_
      --   rw [← pow_mul]
      --   apply pow_le_pow_right' c.one_le_coeffSubmodule
      --   have deg_bound₂ : c'.degBound < c.degBound := by
      --     dsimp [InductionObj.degBound]
      --     gcongr 2 ^ ?_
      --     · exact Nat.lt_succ_self _
      --     apply Finset.sum_lt_sum ?_ ⟨j, Finset.mem_univ _, ?_⟩
      --     · intro k _
      --       rw [Function.update_apply]
      --       split_ifs with hkj
      --       · subst hkj; exact (natDegree_modByMonic_le _ hi).trans (natDegree_le_natDegree hle)
      --       · rfl
      --     · simpa using (natDegree_modByMonic_lt _ hi hi').trans_le (natDegree_le_natDegree hle)
      --   calc  2 ^ (c.val j).natDegree * c'.degBound ^ c'.degBound
      --     _ ≤ c.degBound * c.degBound ^ c'.degBound := by
      --       gcongr
      --       delta InductionObj.degBound
      --       gcongr
      --       · exact Nat.le_succ _
      --       · exact Finset.single_le_sum (f := fun i ↦ ° (c.val i))
      --           (by intros; positivity) (Finset.mem_univ _)
      --     _ = c.degBound ^ (c'.degBound + 1) := by rw [pow_succ']
      --     _ ≤ c.degBound ^ c.degBound := by gcongr <;> omega
      -- rw [coeffSubmodule]
      -- simp only [Submodule.span_le, Set.union_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      --   Set.iUnion_subset_iff, Set.range_subset_iff]
      -- constructor
      -- · apply one_le_pow_of_one_le' c.one_le_coeffSubmodule
      --   rw [Submodule.one_eq_span]
      --   exact Submodule.subset_span rfl
      -- · intro l m
      --   rw [Function.update_apply]
      --   split_ifs with hlj
      --   · refine SetLike.le_def.mp ?_ (modByMonic_mem_span_coeff_pow _ _ _)
      --     gcongr
      --     · apply Submodule.span_mono
      --       refine Set.union_subset_union subset_rfl (Set.union_subset ?_ ?_)
      --       · exact Set.subset_iUnion (fun i ↦ coeff(c.val i)) j
      --       · exact Set.subset_iUnion (fun i ↦ coeff(c.val i)) i
      --   · refine le_self_pow₀ c.one_le_coeffSubmodule (by positivity) ?_
      --     exact Submodule.subset_span (.inr (Set.mem_iUnion_of_mem l ⟨m, rfl⟩))
  · exact induction_aux








      -- rw [InductionObj.coeffSubmodule, Submodule.span_pow, Submodule.span_le]




    -- simp only [Submodule.bot_coe, zeroLocus_singleton_zero, ← Set.compl_eq_univ_diff,
    --   ← basicOpen_eq_zeroLocus_compl]
    -- exact ((isRetroCompact_iff (isOpenMap_comap_C _ (basicOpen f).2)).mpr
    --   ((isCompact_basicOpen f).image (comap C).2)).isConstructible
    --   (isOpenMap_comap_C _ (basicOpen f).2)
  -- · intro R _ c I H₁ H₂ f
  --   replace H₁ := (H₁ (mapRingHom (algebraMap _ _) f)).image_of_isOpenEmbedding
  --     _ (localization_away_isOpenEmbedding (Localization.Away c) c)
  --     (by rw [localization_away_comap_range _ c]
  --         exact (isRetroCompact_iff (basicOpen c).2).mpr (isCompact_basicOpen c))
  --   replace H₂ := (H₂ (mapRingHom (Ideal.Quotient.mk _) f)).image_of_isClosedEmbedding
  --     _ (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective)
  --     (by rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  --         simp only [Ideal.mk_ker, zeroLocus_span, ← basicOpen_eq_zeroLocus_compl]
  --         exact (isRetroCompact_iff (basicOpen c).2).mpr (isCompact_basicOpen c))
  --   rw [comap_C_eq_comap_quotient_union_comap_localization _ c]
  --   simp_rw [Set.preimage_diff, preimage_comap_zeroLocus, Set.image_singleton]
  --   convert H₂.union H₁ using 5 <;>
  --     simp only [Ideal.map, zeroLocus_span, coe_mapRingHom, Ideal.Quotient.algebraMap_eq]

lemma isConstructible_image_comap_C {R} [CommRing R] (s : Set (PrimeSpectrum R[X]))
    (hs : IsConstructible s) :
    IsConstructible (comap C '' s) := by
  apply hs.induction_of_isTopologicalBasis _ isTopologicalBasis_basic_opens
  · intros i s hs
    simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂,
      compl_sdiff_compl, ← zeroLocus_iUnion₂, Set.biUnion_of_singleton]
    rw [← zeroLocus_span]
    apply isConstructible_comap_C_zeroLocus_sdiff_zeroLocus
    exact ⟨hs.toFinset, by simp⟩
  · intros s t hs ht
    rw [Set.image_union]
    exact hs.union ht

lemma isConstructible_image_comap {R S} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : RingHom.FinitePresentation f)
    (s : Set (PrimeSpectrum S)) (hs : IsConstructible s) :
    IsConstructible (comap f '' s) := by
  apply hf.polynomial_induction
    (P := fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (Q := fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
  · exact fun _ ↦ isConstructible_image_comap_C
  · intro R _ S _ f hf hf' s hs
    refine hs.image_of_isClosedEmbedding _ (isClosedEmbedding_comap_of_surjective _ _ hf) ?_
    rw [range_comap_of_surjective _ _ hf, isRetroCompact_iff (isClosed_zeroLocus _).isOpen_compl]
    obtain ⟨t, ht⟩ := hf'
    rw [← ht, ← t.toSet.iUnion_of_singleton_coe, zeroLocus_span, zeroLocus_iUnion, Set.compl_iInter]
    apply isCompact_iUnion
    exact fun _ ↦ by simpa using isCompact_basicOpen _
  · intro R _ S _ T _ f g hf hg s hs
    simp only [comap_comp, ContinuousMap.coe_comp, Set.image_comp]
    exact hf _ (hg _ hs)
  · exact hs
