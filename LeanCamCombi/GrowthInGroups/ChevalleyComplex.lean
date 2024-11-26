import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.DFinsupp.WellFounded
import LeanCamCombi.GrowthInGroups.PrimeSpectrumPolynomial
import LeanCamCombi.Mathlib.Algebra.Polynomial.Degree.Lemmas
import LeanCamCombi.Mathlib.Algebra.Polynomial.Div
import LeanCamCombi.Mathlib.Algebra.Polynomial.Eval.Degree
import LeanCamCombi.Mathlib.Data.Finset.Image
import LeanCamCombi.Mathlib.Data.Prod.Lex
import LeanCamCombi.Mathlib.RingTheory.Localization.Integral

@[gcongr] protected alias ⟨_, GCongr.singleton_subset_singleton⟩ := Set.singleton_subset_singleton

variable {R S M A : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [CommRing A]
  [Algebra R A]

open Function Localization Polynomial TensorProduct PrimeSpectrum
open scoped Pointwise

variable (R) in
@[ext]
structure InductionObj (n : ℕ) where val : Fin n → R[X]

variable {n : ℕ}

instance : CoeFun (InductionObj R n) (fun _ ↦ Fin n → R[X]) := ⟨InductionObj.val⟩

namespace InductionObj

attribute [-instance] AddCommGroup.toIntModule in
attribute [-instance] Ring.toIntAlgebra in
def coeffSubmodule [Algebra ℤ R] (e : InductionObj R n) : Submodule ℤ R :=
  .span ℤ ({1} ∪ ⋃ i, Set.range (e.val i).coeff)

lemma coeffSubmodule_mapRingHom_comp (e : InductionObj R n) (f : R →+* S) :
    ({ val := mapRingHom f ∘ e.val } : InductionObj S n).coeffSubmodule
      = e.coeffSubmodule.map f.toIntAlgHom.toLinearMap := by
  simp [coeffSubmodule, Submodule.map_span, Set.image_insert_eq, Set.image_iUnion, ← Set.range_comp,
    coeff_map_eq_comp]

variable {e T : InductionObj R n}

lemma one_le_coeffSubmodule : 1 ≤ e.coeffSubmodule := by
  rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.subset_span (.inl rfl)

variable (n) in
abbrev DegreeType := (Fin n → WithBot ℕ) ×ₗ Prop

variable (e) in
def degree : DegreeType n :=
  toLex (Polynomial.degree ∘ e.val, ¬ ∃ i, (e.val i).Monic ∧
    ∀ j, e.val j ≠ 0 → (e.val i).degree ≤ (e.val j).degree)

@[simp] lemma ofLex_degree_fst (i) : (ofLex e.degree).fst i = (e.val i).degree := rfl
lemma ofLex_degree_snd : (ofLex e.degree).snd = ¬ ∃ i, (e.val i).Monic ∧
    ∀ j, e.val j ≠ 0 → (e.val i).degree ≤ (e.val j).degree := rfl

variable (e) in
def degBound : ℕ := ∑ i, (e.val i).degree.succ

variable (e) in
def powBound : ℕ := e.degBound ^ e.degBound

lemma powBound_ne_zero : e.powBound ≠ 0 := by
  unfold powBound
  match h : e.degBound with
  | 0 => decide
  | n + 1 => exact (Nat.pow_pos n.succ_pos).ne'

attribute [-instance] Ring.toIntAlgebra in
variable (R n e) in
def InductionStatement [Algebra ℤ R] : Prop :=
  ∀ f, ∃ T : Finset (Σ n, R × (Fin n → R)),
    comap C '' (zeroLocus (Set.range e.val) \ zeroLocus {f}) =
      ⋃ C ∈ T, (zeroLocus (Set.range C.2.2) \ zeroLocus {C.2.1}) ∧
    ∀ C ∈ T, C.1 ≤ e.degBound ∧ ∀ i, C.2.2 i ∈ e.coeffSubmodule ^ e.powBound

local notation3 "coeff("p")" => Set.range (Polynomial.coeff p)

universe u

lemma foo_induction (n : ℕ)
    (P : ∀ (R : Type u) [CommRing R], (InductionObj R n) → Prop)
    (hP₀ : ∀ (R) [CommRing R] (e : InductionObj R n) (i : Fin n),
      (e.1 i).Monic → (∀ j ≠ i, e.1 j = 0) → P R e)
    (hP₁ : ∀ (R) [CommRing R], P R ⟨0⟩)
    (hP₃ : ∀ (R) [CommRing R] (e : InductionObj R n) (i j : Fin n),
      (e.1 i).Monic → (e.1 i).degree ≤ (e.1 j).degree → i ≠ j →
      P R ⟨Function.update e.1 j (e.1 j %ₘ e.1 i)⟩ → P R e)
    (hP : ∀ (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n), c = (e.1 i).leadingCoeff →
      c ≠ 0 →
      P (Away c) ⟨C (IsLocalization.Away.invSelf (S := Away c) c) •
        mapRingHom (algebraMap _ _) ∘ e.val⟩ →
      P (R ⧸ Ideal.span {c}) ⟨mapRingHom (algebraMap _ _) ∘ e.val⟩ → P R e)
    {R} [CommRing R] (e : InductionObj R n) : P R e := by
  classical
  set v := e.degree with hv
  clear_value v
  induction v using WellFoundedLT.induction generalizing R with
  | ind v H_IH =>
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
    -- and `Away (e i).leadingCoeff` where `(e i).leadingCoeff` becomes invertible.
    apply hP _ _ i e rfl (by simpa using hi) (H_IH _ ?_ _ rfl) (H_IH _ ?_ _ rfl)
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

lemma comap_C_eq_comap_localization_union_comap_quotient (s : Set (PrimeSpectrum R[X])) (c : R) :
    .comap C '' s =
      comap (algebraMap R (Away c)) '' (comap C ''
        (comap (mapRingHom (algebraMap R (Away c))) ⁻¹' s)) ∪
      comap (Ideal.Quotient.mk (.span {c})) '' (comap C ''
        (comap (mapRingHom (Ideal.Quotient.mk _)) ⁻¹' s)) := by
  rw [Set.union_comm]
  simp_rw [← Set.image_comp, ← ContinuousMap.coe_comp, ← comap_comp, ← mapRingHom_comp_C,
    comap_comp, ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range,
    ← Set.image_union, ← Set.inter_union_distrib_left]
  letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
  suffices Set.range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) =
      (Set.range (comap (algebraMap R[X] (Away c)[X])))ᶜ by
    rw [this, RingHom.algebraMap_toAlgebra, Set.compl_union_self, Set.inter_univ]
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj, localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

attribute [-instance] AddCommGroup.toIntModule

lemma PrimeSpectrum.zeroLocus_smul_of_isUnit {R} [CommRing R] (s : Set R) {r : R} (hr : IsUnit r) :
    zeroLocus (r • s) = zeroLocus s := by
  ext
  simp [Set.subset_def, ← Set.image_smul, Ideal.unit_mul_mem_iff_mem _ hr]

open IsLocalization in
open Submodule hiding comap in
lemma induction_aux (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n)
      (hi : c = (e.1 i).leadingCoeff) (hc : c ≠ 0) :
      InductionStatement (Away c) n
        ⟨C (IsLocalization.Away.invSelf (S := Away c) c) •
          mapRingHom (algebraMap _ _) ∘ e.val⟩ →
      InductionStatement (R ⧸ Ideal.span {c}) n ⟨mapRingHom (algebraMap _ _) ∘ e.val⟩ →
        InductionStatement R n e := by
  set q₁ := IsScalarTower.toAlgHom ℤ R (Away c)
  set q₂ := Ideal.Quotient.mk (.span {c})
  have q₂_surjective : Surjective q₂ := Ideal.Quotient.mk_surjective
  set e₁ : InductionObj (Away c) n :=
    ⟨C (IsLocalization.Away.invSelf (S := Away c) c) • mapRingHom q₁ ∘ e.val⟩
  set e₂ : InductionObj (R ⧸ Ideal.span {c}) n := ⟨mapRingHom q₂ ∘ e.val⟩
  have degBound_e₁_le : e₁.degBound ≤ e.degBound := by
    unfold degBound; gcongr with j; exact (degree_C_mul_le _ _).trans (degree_map_le _ _)
  have degBound_e₂_lt : e₂.degBound < e.degBound := by
    unfold degBound
    refine Fintype.sum_strictMono <| Pi.lt_def.2 ⟨fun j ↦ ?_, i, ?_⟩
    · dsimp
      gcongr
      exact degree_map_le _ _
    · gcongr
      exact degree_map_lt (by simp [q₂, ← hi]) (by simpa [hi] using hc)
  intro (H₁ : InductionStatement _ _ e₁) (H₂ : InductionStatement _ _ e₂) f
  obtain ⟨T₁, hT₁⟩ := H₁ (mapRingHom q₁ f)
  obtain ⟨T₂, hT₂⟩ := H₂ (mapRingHom q₂ f)
  simp only [forall_and] at hT₁ hT₂
  obtain ⟨hT₁, hT₁deg, hT₁span⟩ := hT₁
  obtain ⟨hT₂, hT₂deg, hT₂span⟩ := hT₂
  -- Lift the tuples of `T₁` from `Away c` to `R`
  let _ : Invertible (q₁ c) :=
    -- TODO(Andrew): add API for `IsLocalization.Away.invSelf`
    ⟨IsLocalization.Away.invSelf c, by simp [q₁, IsLocalization.Away.invSelf], by
      simp [q₁, IsLocalization.Away.invSelf]⟩
  have he₁span :
      e₁.coeffSubmodule ^ e₁.powBound = ⅟(q₁ c ^ e₁.powBound) •
        (span ℤ ({c} ∪ ⋃ i, coeff(e.val i)) ^ e₁.powBound).map q₁.toLinearMap := by
    unfold coeffSubmodule
    rw [Submodule.map_pow, map_span, invOf_pow, ← smul_pow, ← span_smul]
    simp [Set.image_insert_eq, Set.smul_set_insert, Set.image_iUnion, Set.smul_set_iUnion, q₁]
    congr! with i
    change _ = IsLocalization.Away.invSelf c • _
    simp [← Set.range_comp, Set.smul_set_range, funext fun _ ↦ coeff_C_mul _]
    ext
    simp [q₁]
  replace hT₁span x hx i :=
    smul_mem_pointwise_smul _ (q₁ c ^ e₁.powBound) _ (hT₁span x hx i)
  simp only [he₁span, smul_invOf_smul, smul_eq_mul] at hT₁span
  choose! g₁ hg₁ hq₁g₁ using hT₁span
  -- Lift the constants of `T₁` from `Away c` to `R`
  choose! n₁ f₁ hf₁ using Away.surj (S := Away c) c
  change (∀ _, _ * q₁ _ ^ _ = q₁ _) at hf₁
  -- Lift the tuples of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  let _ : Algebra ℤ R := Ring.toIntAlgebra _
  rw [coeffSubmodule_mapRingHom_comp, ← Submodule.map_pow] at hT₂span
  choose! g₂ hg₂ hq₂g₂ using hT₂span
  -- Lift the constants of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  choose! f₂ hf₂ using Ideal.Quotient.mk_surjective (I := .span {c})
  change (∀ _, q₂ _ = _) at hf₂
  -- Lift everything together
  classical
  let S₁ : Finset (Σ n, R × (Fin n → R)) := T₁.image fun x ↦ ⟨_, (c * f₁ x.2.1, g₁ x)⟩
  let S₂ : Finset (Σ n, R × (Fin n → R)) := T₂.image fun x ↦ ⟨_, (f₂ x.2.1, Fin.cons c (g₂ x))⟩
  refine ⟨S₁ ∪ S₂, ?_, ?_⟩
  · calc
      comap C '' (zeroLocus (.range e.val) \ zeroLocus {f})
        = comap q₁ '' (comap C ''
            (comap (mapRingHom q₁.toRingHom) ⁻¹' (zeroLocus (.range e.val) \ zeroLocus {f}))) ∪
          comap q₂ '' (comap C ''
            (comap (mapRingHom q₂) ⁻¹' (zeroLocus (.range e.val) \ zeroLocus {f}))) :=
        comap_C_eq_comap_localization_union_comap_quotient _ c
      _ = (⋃ C ∈ S₁, zeroLocus (Set.range C.snd.2) \ zeroLocus {C.snd.1}) ∪
          ⋃ C ∈ S₂, zeroLocus (Set.range C.snd.2) \ zeroLocus {C.snd.1} := ?_
      _ = ⋃ C ∈ S₁ ∪ S₂, zeroLocus (Set.range C.snd.2) \ zeroLocus {C.snd.1} := by
        simpa using (Set.biUnion_union S₁.toSet S₂ _).symm
    congr 1
    · convert congr(comap q₁.toRingHom '' $hT₁)
      · rw [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
          Set.image_singleton, Pi.smul_def, ← Set.smul_set_range, Set.range_comp]
        congr 1
        refine (PrimeSpectrum.zeroLocus_smul_of_isUnit _ ?_).symm
        apply IsUnit.map
        exact isUnit_iff_exists_inv'.mpr ⟨_, IsLocalization.Away.mul_invSelf c⟩
      · rw [Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₁, Finset.coe_image, Set.biUnion_image]
        congr! with x hxT₁
        apply Set.injOn_preimage subset_rfl (f := comap q₁.toRingHom)
        · erw [localization_away_comap_range (S := Localization.Away c) (r := c)]
          rw [sdiff_eq, ← basicOpen_eq_zeroLocus_compl, basicOpen_mul]
          exact Set.inter_subset_right.trans Set.inter_subset_left
        · exact Set.image_subset_range _ _
        · rw [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
            Set.preimage_image_eq]
          swap; · exact (localization_specComap_injective _ (.powers c))
          simp only [AlgHom.toLinearMap_apply] at hq₁g₁
          simp_rw [← Set.range_comp, Function.comp_def]
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hq₁g₁ _ hxT₁, Set.image_singleton,
            map_mul, ← hf₁]
          rw [mul_comm x.2.1, ← mul_assoc, ← pow_succ']
          conv_rhs => rw [← PrimeSpectrum.zeroLocus_smul_of_isUnit _
            ((isUnit_of_invertible (q₁ c)).pow e₁.powBound),
            ← PrimeSpectrum.zeroLocus_smul_of_isUnit {_}
            ((isUnit_of_invertible (q₁ c)).pow (n₁ x.2.1 + 1))]
          simp only [Set.smul_set_singleton, smul_eq_mul]
          simp only [← Set.image_smul, ← Set.range_comp]
          rfl
    · convert congr(comap q₂ '' $hT₂)
      · rw [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
          Set.image_singleton, Set.range_comp]
      · rw [Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₂, Finset.coe_image, Set.biUnion_image]
        congr! 3 with x hxT₂
        apply Set.injOn_preimage subset_rfl (f := comap q₂)
        · rw [range_comap_of_surjective _ _ q₂_surjective]
          simp only [Ideal.mk_ker, zeroLocus_span, q₂]
          exact Set.diff_subset.trans (zeroLocus_anti_mono (by simp))
        · exact Set.image_subset_range _ _
        · simp only [AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe] at hq₂g₂
          have : q₂ c = 0 := by simp [q₂]
          simp only [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
            Set.preimage_image_eq _ (comap_injective_of_surjective _ q₂_surjective)]
          simp only [Fin.range_cons, Set.image_singleton, hf₂, Set.image_insert_eq,
            ← Set.range_comp, Function.comp_def, hq₂g₂ _ hxT₂]
          rw [← Set.union_singleton, zeroLocus_union, this,
            zeroLocus_singleton_zero, Set.inter_univ]
  · simp only [Finset.mem_union, forall_and, or_imp, Finset.forall_mem_image, S₁, S₂]
    refine ⟨⟨fun x hx ↦ (hT₁deg _ hx).trans degBound_e₁_le,
      fun x hx ↦ (hT₂deg _ hx).trans_lt degBound_e₂_lt⟩,
      fun x hx k ↦ SetLike.mem_of_subset ?_ (hg₁ _ hx _),
      fun x hx ↦ Fin.cons ?_ fun k ↦ SetLike.mem_of_subset ?_ (hg₂ _ hx _)⟩
    · norm_cast
      calc
        span ℤ ({c} ∪ ⋃ i, coeff(e.val i)) ^ e₁.powBound
        _ ≤ span ℤ (⋃ i, coeff(e.val i)) ^ e₁.powBound := by
          gcongr; simpa [Set.insert_subset_iff] using ⟨_, _, hi.symm⟩
        _ ≤ e.coeffSubmodule ^ e.powBound := by
          unfold coeffSubmodule powBound
          gcongr
          · exact one_le_coeffSubmodule
          · exact Set.subset_union_right
          · omega
    · exact le_self_pow₀ one_le_coeffSubmodule powBound_ne_zero <| subset_span <| .inr <| by
        simpa using ⟨_, _, hi.symm⟩
    · unfold powBound
      gcongr
      · exact one_le_coeffSubmodule
      · omega

lemma isConstructible_comap_C_zeroLocus_sdiff_zeroLocus :
    ∀ S : InductionObj R n, InductionStatement R n S := by
  classical
  apply foo_induction
  · intros R _ g i hi hi_min f
    let M := R[X] ⧸ Ideal.span {g.1 i}
    have : Module.Free R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    have : Module.Finite R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    refine ⟨(Finset.range (Module.finrank R M)).image
      fun j ↦ ⟨0, (Algebra.lmul R M (Ideal.Quotient.mk _ f)).charpoly.coeff j, 0⟩, ?_, ?_⟩
    · ext x
      have : zeroLocus (Set.range g.val) = zeroLocus {g.1 i} := by
        rw [Set.range_eq_iUnion, zeroLocus_iUnion]
        refine (Set.iInter_subset _ _).antisymm (Set.subset_iInter fun j ↦ ?_)
        by_cases hij : i = j
        · subst hij; rfl
        · rw [hi_min j (.symm hij), zeroLocus_singleton_zero]; exact Set.subset_univ _
      rw [this, ← Polynomial.algebraMap_eq, mem_image_comap_zeroLocus_sdiff,
        IsScalarTower.algebraMap_apply R[X] M, isNilpotent_tensor_residueField_iff]
      simp [Set.subset_def, M]
    · simp
  · intro R _ f
    refine ⟨(Finset.range (f.natDegree + 2)).image fun j ↦ ⟨0, f.coeff j, 0⟩, ?_, ?_⟩
    · convert image_comap_C_basicOpen f
      · simp only [basicOpen_eq_zeroLocus_compl, Set.compl_eq_univ_diff]
        congr 1
        rw [← Set.univ_subset_iff]
        rintro x _ _ ⟨_, rfl⟩
        exact zero_mem x.asIdeal
      · suffices Set.range f.coeff = ⋃ i < f.natDegree + 2, {f.coeff i} by
          simp [← Set.compl_eq_univ_diff, eq_compl_comm (y := zeroLocus _),
            ← zeroLocus_iUnion₂, this]
        trans f.coeff '' (Set.Iio (f.natDegree + 2))
        · refine ((Set.image_subset_range _ _).antisymm ?_).symm
          rintro _ ⟨i, rfl⟩
          by_cases hi : i ≤ f.natDegree
          · exact ⟨i, hi.trans_lt (by simp), rfl⟩
          · exact ⟨f.natDegree + 1, by simp,
              by simp [f.coeff_eq_zero_of_natDegree_lt (lt_of_not_le hi)]⟩
        · ext; simp [eq_comm]
    · simp
  · intro R _ c i j hi hle hne H f
    cases subsingleton_or_nontrivial R
    · use ∅
      simp [Subsingleton.elim f 0]
    obtain ⟨S, hS, hS'⟩ := H f
    refine ⟨S, Eq.trans ?_ hS, ?_⟩
    · rw [← zeroLocus_span (Set.range _), ← zeroLocus_span (Set.range _),
        Ideal.span_range_update_divByMonic _ _ _ hne hi]
    · intro C hC
      let c' : InductionObj _ _ := ⟨Function.update c.val j (c.val j %ₘ c.val i)⟩
      have deg_bound₁ : c'.degBound ≤ c.degBound := by
        dsimp [InductionObj.degBound]
        gcongr with k
        · rw [Function.update_apply]
          split_ifs with hkj
          · subst hkj; exact (degree_modByMonic_le _ hi).trans hle
          · rfl
      refine ⟨(hS' C hC).1.trans deg_bound₁, fun k ↦ SetLike.le_def.mp ?_ ((hS' C hC).2 k)⟩
      show c'.coeffSubmodule ^ c'.powBound ≤ _
      delta powBound
      suffices hij : c'.coeffSubmodule ≤ c.coeffSubmodule ^ (c.val j).degree.succ by
        by_cases hi' : c.val i = 1
        · gcongr
          · exact c.one_le_coeffSubmodule
          · refine Submodule.span_le.mpr (Set.union_subset ?_ ?_)
            · exact Set.subset_union_left.trans Submodule.subset_span
            · refine Set.iUnion_subset fun k ↦ ?_
              simp only [Function.update_apply, hi', modByMonic_one]
              split_ifs
              · rintro _ ⟨_, rfl⟩
                exact zero_mem _
              · exact (Set.subset_iUnion (fun i ↦ coeff(c.val i)) k).trans
                  (Set.subset_union_right.trans Submodule.subset_span)
          rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, InductionObj.degBound]
          refine Fintype.sum_pos (Pi.lt_def.mpr ⟨by positivity, i, by simp [hi']⟩)
        refine (pow_le_pow_left' hij _).trans ?_
        rw [← pow_mul]
        apply pow_le_pow_right' c.one_le_coeffSubmodule
        have deg_bound₂ : c'.degBound < c.degBound := by
          dsimp [InductionObj.degBound]
          apply Finset.sum_lt_sum ?_ ⟨j, Finset.mem_univ _, ?_⟩
          · intro k _
            rw [Function.update_apply]
            split_ifs with hkj
            · subst hkj; gcongr; exact (degree_modByMonic_le _ hi).trans hle
            · rfl
          · gcongr; simpa using (degree_modByMonic_lt _ hi).trans_le hle
        calc  (c.val j).degree.succ * c'.degBound ^ c'.degBound
          _ ≤ c.degBound * c.degBound ^ c'.degBound := by
            gcongr
            delta InductionObj.degBound
            exact Finset.single_le_sum (f := fun i ↦ (c.val i).degree.succ)
              (by intros; positivity) (Finset.mem_univ _)
          _ = c.degBound ^ (c'.degBound + 1) := by rw [pow_succ']
          _ ≤ c.degBound ^ c.degBound := by gcongr <;> omega
      rw [coeffSubmodule]
      simp only [Submodule.span_le, Set.union_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        Set.iUnion_subset_iff, Set.range_subset_iff]
      constructor
      · apply one_le_pow_of_one_le' c.one_le_coeffSubmodule
        rw [Submodule.one_eq_span]
        exact Submodule.subset_span rfl
      · intro l m
        rw [Function.update_apply]
        split_ifs with hlj
        · refine SetLike.le_def.mp ?_ (modByMonic_mem_span_coeff_pow' _ _ _)
          unfold coeffSubmodule
          gcongr
          · refine Set.union_subset ?_ ?_
            · exact Set.subset_iUnion (fun i ↦ coeff(c.val i)) j
            · exact Set.subset_iUnion (fun i ↦ coeff(c.val i)) i
        · have : (c.val j).degree.succ ≠ 0 := by
            rw [← Nat.pos_iff_ne_zero]
            apply WithBot.succ_lt_succ (a := ⊥)
            refine lt_of_lt_of_le ?_ hle
            rw [bot_lt_iff_ne_bot, ne_eq, degree_eq_bot]
            intro e
            simp [e] at hi
          refine le_self_pow₀ c.one_le_coeffSubmodule this ?_
          exact Submodule.subset_span (.inr (Set.mem_iUnion_of_mem l ⟨m, rfl⟩))
  · convert induction_aux (n := n) -- Andrew: this is absolutely fine if you ignore it
    ext
    exact (OreLocalization.zsmul_eq_zsmul _ _).symm

variable (R) in
abbrev ConstructibleSetData := Finset (Σ n, R × (Fin n → R))

def ConstructibleSetData.toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) :=
  ⋃ x ∈ S, zeroLocus (Set.range x.2.2) \ zeroLocus {x.2.1}

def ConstructibleSetData.degBound (S : ConstructibleSetData R[X]) : ℕ :=
  S.sup fun e ↦ ∑ i, (e.2.2 i).degree.succ

def ConstructibleSetData.mvDegBound {σ} (S : ConstructibleSetData (MvPolynomial σ R)) : ℕ :=
  S.sup fun e ↦ ∑ i, (e.2.2 i).totalDegree.succ

lemma exists_constructibleSetData_comap_C_toSet_eq_toSet {R} [CommRing R]
    (M : Submodule ℤ R) (hM : 1 ∈ M)
    (S : ConstructibleSetData R[X]) (hS : ∀ x ∈ S, ∀ j k, (x.2.2 j).coeff k ∈ M) :
    ∃ T : ConstructibleSetData R,
      comap C '' S.toSet = T.toSet ∧ ∀ C ∈ T, C.1 ≤ S.degBound ∧
      ∀ i, C.2.2 i ∈ M ^ S.degBound ^ S.degBound := by
  classical
  have H (x) (hx : x ∈ S) := isConstructible_comap_C_zeroLocus_sdiff_zeroLocus ⟨x.2.2⟩ x.2.1
  choose! f hf₁ hf₂ hf₃ using H
  refine ⟨Finset.biUnion S f, ?_, ?_⟩
  · simp only [ConstructibleSetData.toSet, Set.image_iUnion, Finset.set_biUnion_biUnion]
    congr! with x hx
    exact hf₁ x hx
  · simp only [Finset.mem_biUnion, Prod.exists, forall_exists_index, and_imp]
    intros x y hy hx
    have H : degBound ⟨y.snd.2⟩ ≤ S.degBound :=
      Finset.le_sup (f := fun e ↦ ∑ i, (e.2.2 i).degree.succ) hy
    refine ⟨(hf₂ y hy x hx).trans H, fun i ↦ SetLike.le_def.mp ?_ (hf₃ y hy x hx i)⟩
    gcongr
    · simpa [Submodule.one_eq_span]
    · refine Submodule.span_le.mpr ?_
      simp [Set.subset_def, hM, forall_comm (α := R), hS y hy]
    · delta powBound
      by_cases h : S.degBound = 0
      · have : degBound ⟨y.snd.2⟩ = 0 := by nlinarith
        rw [h, this]
      gcongr
      rwa [Nat.one_le_iff_ne_zero]

lemma exists_constructibleSetData_comap_C_toSet_eq_toSet' {R σ} [CommRing R]
    (M : Submodule ℤ R) (hM : 1 ∈ M)
    (S : ConstructibleSetData (MvPolynomial σ R)) (hS : ∀ x ∈ S, ∀ j k, (x.2.2 j).coeff k ∈ M) :
    ∃ T : ConstructibleSetData R,
      comap MvPolynomial.C '' S.toSet = T.toSet ∧ ∀ C ∈ T, C.1 ≤ S.mvDegBound ∧
      ∀ i, C.2.2 i ∈ M ^ S.mvDegBound ^ S.mvDegBound := sorry
