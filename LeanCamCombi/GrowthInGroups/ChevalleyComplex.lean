import Mathlib.Algebra.Order.Star.Basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdjoinRoot
import LeanCamCombi.Mathlib.Algebra.Polynomial.Eval
import LeanCamCombi.Mathlib.Data.Fintype.Card
import LeanCamCombi.Mathlib.Data.Prod.Lex
import LeanCamCombi.Mathlib.Order.RelClasses
import LeanCamCombi.GrowthInGroups.PolynomialLocalization
import LeanCamCombi.GrowthInGroups.PrimeSpectrumPolynomial

variable {R M A} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

open Polynomial TensorProduct PrimeSpectrum

@[ext]
structure InductionObj (R) [CommRing R] (n : ℕ) where
  val : Fin n → R[X]

variable {n : ℕ} (S T : InductionObj R n)

instance : CoeFun (InductionObj R n) (fun _ ↦ Fin n → R[X]) := ⟨InductionObj.val⟩

namespace InductionObj

def coeffSubmodule : Submodule ℤ R := Submodule.span ℤ ({1} ∪ ⋃ i, Set.range (S.val i).coeff)

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

lemma foo_induction (n : ℕ)
    (P : ∀ (R : Type u) [CommRing R], (InductionObj R n) → Prop)
    (hP₀ : ∀ (R) [CommRing R] (e : InductionObj R n) (i : Fin n),
      (e.1 i).Monic → (∀ j ≠ i, e.1 j = 0) → P R e)
    (hP₁ : ∀ (R) [CommRing R], P R ⟨0⟩)
    (hP₃ : ∀ (R) [CommRing R] (e : InductionObj R n) (i j : Fin n),
      (e.1 i).Monic → (e.1 i).degree ≤ (e.1 j).degree → i ≠ j →
      P R ⟨Function.update e.1 j (e.1 j %ₘ e.1 i)⟩ → P R e)
    (hP : ∀ (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n), c = (e.1 i).leadingCoeff →
      P (Localization.Away c) ⟨C (IsLocalization.Away.invSelf (S := Localization.Away c) c) •
        mapRingHom (algebraMap _ _) ∘ e.val⟩ →
      P (R ⧸ Ideal.span {c}) ⟨mapRingHom (algebraMap _ _) ∘ e.val⟩ → P R e)
    {R} [CommRing R] (e : InductionObj R n) : P R e := by
  classical
  set v := e.degree with hv
  clear_value v
  induction v using WellFoundedLT.induction' generalizing R with
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
