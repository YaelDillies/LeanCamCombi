import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.DFinsupp.WellFounded
import LeanCamCombi.Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanCamCombi.Mathlib.Algebra.Polynomial.Degree.Lemmas
import LeanCamCombi.Mathlib.Algebra.Polynomial.Degree.Operations
import LeanCamCombi.Mathlib.Algebra.Polynomial.Div
import LeanCamCombi.Mathlib.Algebra.Polynomial.Eval.Degree
import LeanCamCombi.Mathlib.Data.Finset.Image
import LeanCamCombi.Mathlib.Data.Prod.Lex
import LeanCamCombi.Mathlib.Data.Set.Pointwise.SMul
import LeanCamCombi.Mathlib.RingTheory.Localization.Integral
import LeanCamCombi.GrowthInGroups.PrimeSpectrumPolynomial
import LeanCamCombi.GrowthInGroups.WithBotSucc

variable {R S M A : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [CommRing A]
  [Algebra R A]

open Localization Polynomial TensorProduct PrimeSpectrum
open scoped Pointwise

@[ext]
structure InductionObj (R) [CommRing R] (n : ℕ) where
  val : Fin n → R[X]

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

attribute [-instance] Ring.toIntAlgebra in
variable (R n e) in
def InductionStatement [Algebra ℤ R] : Prop :=
  ∀ f, ∃ T : Finset (Σ n, R × (Fin n → R)),
    comap C '' (zeroLocus (Set.range e.val) \ zeroLocus {f}) =
      ⋃ C ∈ T, (zeroLocus (Set.range C.2.2) \ zeroLocus {C.2.1}) ∧
    ∀ C ∈ T, C.1 ≤ e.degBound ∧ ∀ i, C.2.2 i ∈ e.coeffSubmodule ^ e.powBound

local notation "°" => Polynomial.natDegree
local notation "↝" => Polynomial.leadingCoeff
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
  set e₁ : InductionObj (Away c) n :=
    ⟨C (IsLocalization.Away.invSelf (S := Away c) c) • mapRingHom q₁ ∘ e.val⟩
  set e₂ : InductionObj (R ⧸ Ideal.span {c}) n := ⟨mapRingHom q₂ ∘ e.val⟩
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
  choose g₁ hg₁ using hT₁span
  -- Lift the constants of `T₁` from `Away c` to `R`
  choose n₁ f₁ hf₁ using Away.surj (S := Away c) c
  -- Lift the tuples of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  let _ : Algebra ℤ R := Ring.toIntAlgebra _
  rw [coeffSubmodule_mapRingHom_comp, ← Submodule.map_pow] at hT₂span
  choose g₂ hg₂ using hT₂span
  -- Lift the constants of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  choose f₂ hf₂ using Ideal.Quotient.mk_surjective (I := .span {c})
  -- Lift everything together
  classical
  let S₁ : Finset (Σ n, R × (Fin n → R)) :=
    T₁.attach.image fun x ↦ ⟨_, (f₁ x.1.2.1, g₁ x.1 x.2)⟩
  let S₂ : Finset (Σ n, R × (Fin n → R)) :=
    T₂.attach.image fun x ↦ ⟨_, (c * f₂ x.1.2.1, Fin.cons c (g₂ x.1 x.2))⟩
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
        -- not Yaël-trivial, but Andrew-trivial
        sorry
      · rw [Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₁, Finset.coe_image, Set.biUnion_image]
        -- `attach` nonsense + some actual math
        sorry
    · convert congr(comap q₂ '' $hT₂)
      · rw [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
          Set.image_singleton, Set.range_comp]
      · rw [Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₂, Finset.coe_image, Set.biUnion_image]
        -- `attach` nonsense + some actual math
        sorry
  · simp only [Finset.mem_union, Finset.forall_mem_image, Finset.mem_attach, true_and, forall_and,
      or_imp, forall_exists_index, S₁, S₂, Subtype.forall, forall_const]
    -- `attach` nonsense here
    refine ⟨⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · calc
        x.1 ≤ e₁.degBound := hT₁deg _ hx
        _ ≤ e.degBound := by
          simp [InductionObj.degBound]
          gcongr with j
          exact (degree_C_mul_le _ _).trans (degree_map_le _ _)
    · calc
        x.1 + 1 ≤ e₂.degBound + 1 := by gcongr; exact hT₂deg _ hx
        _ ≤ e.degBound := by
          simp [InductionObj.degBound, Nat.succ_le_iff]
          refine Fintype.sum_lt_sum (fun j ↦ by gcongr; exact degree_map_le _ _) ⟨i, ?_⟩
          gcongr
          refine degree_map_lt (by simp [q₂, ← hi]) (by simpa [hi] using hc)
    · sorry
    · sorry

lemma isConstructible_comap_C_zeroLocus_sdiff_zeroLocus {R} [CommRing R] {n}
    (S : InductionObj R n) : InductionStatement R n S := by
  classical
  revert S
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
        · refine le_self_pow₀ c.one_le_coeffSubmodule (by sorry) ?_
          exact Submodule.subset_span (.inr (Set.mem_iUnion_of_mem l ⟨m, rfl⟩))
  · convert induction_aux (n := n) -- Andrew: this is absolutely fine if you ignore it
    ext
    exact (OreLocalization.zsmul_eq_zsmul _ _).symm
