import Mathlib
import LeanCamCombi.Mathlib.Data.Prod.Lex
import LeanCamCombi.Mathlib.RingTheory.Ideal.Span
import LeanCamCombi.GrowthInGroups.Constructible

variable {R M A} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

open Polynomial TensorProduct PrimeSpectrum

abbrev Ideal.ResidueField (I : Ideal R) [I.IsPrime] : Type _ :=
  LocalRing.ResidueField (Localization.AtPrime I)

lemma LocalRing.residue_surjective {R} [CommRing R] [LocalRing R] :
    Function.Surjective (LocalRing.residue R) :=
  Ideal.Quotient.mk_surjective

instance {R S} [CommRing R] [CommRing S] [LocalRing S] [Algebra R S] :
    Algebra R (LocalRing.ResidueField S) := by delta LocalRing.ResidueField; infer_instance

@[simp]
lemma LocalRing.algebraMap_residueField {R} [CommRing R] [LocalRing R] :
    algebraMap R (LocalRing.ResidueField R) = LocalRing.residue R := rfl

instance {R₁ R₂ S} [CommRing R₁] [CommRing R₂] [CommRing S] [LocalRing S]
    [Algebra R₁ R₂] [Algebra R₁ S] [Algebra R₂ S] [IsScalarTower R₁ R₂ S] :
    IsScalarTower R₁ R₂ (LocalRing.ResidueField S) := by
  delta LocalRing.ResidueField; infer_instance

noncomputable
abbrev Ideal.residueFieldMap (I : Ideal R) [I.IsPrime] (J : Ideal A) [J.IsPrime]
    (f : R →+* A) (hf : I = J.comap f) : I.ResidueField →+* J.ResidueField :=
  LocalRing.ResidueField.map (Localization.localRingHom I J f hf)

noncomputable
def Ideal.residueFieldMapₐ (I : Ideal R) [I.IsPrime] (J : Ideal A) [J.IsPrime]
    (hf : I = J.comap (algebraMap R A)) : I.ResidueField →ₐ[R] J.ResidueField where
  __ := Ideal.residueFieldMap I J (algebraMap R A) hf
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I),
      LocalRing.algebraMap_residueField]
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, LocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
    rfl

@[simp]
lemma Ideal.algebraMap_residueField_eq_zero {I : Ideal R} [I.IsPrime] {x} :
    algebraMap R I.ResidueField x = 0 ↔ x ∈ I := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I),
    LocalRing.algebraMap_residueField, LocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _

lemma Ideal.ker_algebraMap_residueField (I : Ideal R) [I.IsPrime] :
    RingHom.ker (algebraMap R I.ResidueField) = I := by
  ext x
  exact Ideal.algebraMap_residueField_eq_zero


-- set_option
-- set_option synthInstance.maxHeartbeats 400000 in
-- noncomputable
-- instance (g : R[X]) (x : Ideal R) [x.IsPrime] :
--     Algebra R[X] (Module.End R[X] ((R[X] ⧸ Ideal.span {g}) ⊗[R] x.ResidueField)) :=
--   inferInstance

noncomputable
def fooBarMap (s : Set A) (I : Ideal A) (hg : s ⊆ I) [I.IsPrime] :
    (A ⧸ Ideal.span s) ⊗[R] (I.comap (algebraMap R A)).ResidueField →ₐ[A] I.ResidueField := by
  fapply Algebra.TensorProduct.lift
  · refine Ideal.Quotient.liftₐ (Ideal.span s) (Algebra.ofId A I.ResidueField) ?_
    show Ideal.span s ≤ RingHom.ker (algebraMap A I.ResidueField)
    rwa [Ideal.span_le, Ideal.ker_algebraMap_residueField]
  · exact Ideal.residueFieldMapₐ _ _ rfl
  · exact fun _ _ ↦ .all _ _

-- set_option synthInstance.maxHeartbeats 400000 in
-- -- set_option maxHeartbeats 0 in
lemma mem_image_comap_zeroLocus_sdiff (f : A) (s : Set A) (x) :
    x ∈ comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) ↔
      ¬ IsNilpotent (algebraMap A ((A ⧸ Ideal.span s) ⊗[R] x.asIdeal.ResidueField) f) := by
  constructor
  · rintro ⟨q, ⟨hqg, hqf⟩, rfl⟩ H
    simp only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hqg hqf
    have := H.map (fooBarMap s q.asIdeal hqg)
    rw [AlgHom.commutes, isNilpotent_iff_eq_zero, ← RingHom.mem_ker,
      Ideal.ker_algebraMap_residueField] at this
    exact hqf this
  · intro H
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at H
    simp only [Set.mem_setOf_eq, Algebra.TensorProduct.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, not_forall, Classical.not_imp] at H
    obtain ⟨q, hq, hfq⟩ := H
    have : ∀ a ∈ s, Ideal.Quotient.mk (Ideal.span s) a ⊗ₜ[R] 1 ∈ q := fun a ha ↦ by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ha)]
    refine ⟨comap (algebraMap A _) ⟨q, hq⟩, ⟨by simpa [Set.subset_def], by simpa⟩, ?_⟩
    rw [← comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      ← Algebra.TensorProduct.includeRight.comp_algebraMap, comap_comp_apply,
      Subsingleton.elim (α := PrimeSpectrum x.asIdeal.ResidueField) (comap _ _) ⊥]
    ext a
    exact congr(a ∈ $(Ideal.ker_algebraMap_residueField _))

lemma mem_image_comap_basicOpen (f : A) (x) :
    x ∈ comap (algebraMap R A) '' (basicOpen f) ↔
      ¬ IsNilpotent (algebraMap A (A ⊗[R] x.asIdeal.ResidueField) f) := by
  have e : A ⊗[R] x.asIdeal.ResidueField ≃ₐ[A]
      (A ⧸ (Ideal.span ∅ : Ideal A)) ⊗[R] x.asIdeal.ResidueField := by
    refine Algebra.TensorProduct.congr ?f AlgEquiv.refl
    rw [Ideal.span_empty]
    exact { __ := (RingEquiv.quotientBot A).symm, __ := Algebra.ofId _ _ }
  rw [← IsNilpotent.map_iff e.injective, AlgEquiv.commutes,
    ← mem_image_comap_zeroLocus_sdiff f ∅ x, zeroLocus_empty, ← Set.compl_eq_univ_diff,
    basicOpen_eq_zeroLocus_compl]

lemma mem_image_comap_basicOpen_iff_map_ne_zero (f : R[X]) (x : PrimeSpectrum R) :
    x ∈ comap C '' (basicOpen f) ↔ f.map (algebraMap R x.asIdeal.ResidueField) ≠ 0 := by
  refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
  let e : R[X] ⊗[R] x.asIdeal.ResidueField ≃ₐ[R] x.asIdeal.ResidueField[X] :=
    (Algebra.TensorProduct.comm R _ _).trans (polyEquivTensor R x.asIdeal.ResidueField).symm
  rw [← IsNilpotent.map_iff e.injective, isNilpotent_iff_eq_zero]
  show (e.toAlgHom.toRingHom).comp (algebraMap _ _) f = 0 ↔ Polynomial.mapRingHom _ f = 0
  congr!
  ext1
  · ext; simp [e]
  · simp [e, monomial_one_one_eq_X]


lemma image_comap_C_basicOpen (f : R[X]) :
      comap C '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ := by
    ext p
    rw [mem_image_comap_basicOpen_iff_map_ne_zero, ← not_iff_not]
    simp [Polynomial.ext_iff, Set.range_subset_iff]

lemma isOpenMap_comap_C : IsOpenMap (comap (R := R) C) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl


open Module in
lemma LinearMap.nilpotent_iff_charpoly {R M} [CommRing R] [IsDomain R] [AddCommGroup M]
  [Module R M] [Free R M] [IsNoetherian R M] (φ : End R M) :
    IsNilpotent φ ↔ charpoly φ = X ^ finrank R M :=
  (LinearMap.charpoly_nilpotent_tfae φ).out 0 1

lemma LinearMap.charpoly_baseChange {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    {A} [CommRing A] [Algebra R A] (f : M →ₗ[R] M) :
    (f.baseChange A).charpoly = f.charpoly.map (algebraMap R A) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  let I := Module.Free.ChooseBasisIndex R M
  let b : Basis I R M := Module.Free.chooseBasis R M
  rw [← f.charpoly_toMatrix b, ← (f.baseChange A).charpoly_toMatrix (b.baseChange A),
    ← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [Matrix.map_apply, LinearMap.toMatrix_apply, ← Algebra.algebraMap_eq_smul_one]

lemma Algebra.baseChange_lmul {R B} [CommRing R] [CommRing B] [Algebra R B]
    {A} [CommRing A] [Algebra R A] (f : B) :
    (Algebra.lmul R B f).baseChange A = Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ f) := by
  ext i
  simp

lemma isNilpotent_tensor_residueField_iff
    [Module.Free R A] [Module.Finite R A] (f : A) (I : Ideal R) [I.IsPrime] :
    IsNilpotent (algebraMap A (A ⊗[R] I.ResidueField) f) ↔
      ∀ i < Module.finrank R A, (Algebra.lmul R A f).charpoly.coeff i ∈ I := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R (A ⊗[R] I.ResidueField)).codomain_trivial
    simp [Subsingleton.elim I ⊤, Subsingleton.elim (f ⊗ₜ[R] (1 : I.ResidueField)) 0]
  have : Module.finrank I.ResidueField (I.ResidueField ⊗[R] A) = Module.finrank R A := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  rw [← IsNilpotent.map_iff (Algebra.TensorProduct.comm R A I.ResidueField).injective]
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
    Algebra.coe_lmul_eq_mul, Algebra.TensorProduct.comm_tmul]
  rw [← IsNilpotent.map_iff (Algebra.lmul_injective (R := I.ResidueField)),
    LinearMap.nilpotent_iff_charpoly, ← Algebra.baseChange_lmul, LinearMap.charpoly_baseChange]
  simp_rw [this, ← ((LinearMap.mul R A) f).charpoly_natDegree]
  constructor
  · intro e i hi
    replace e := congr(($e).coeff i)
    simpa only [Algebra.coe_lmul_eq_mul, coeff_map, coeff_X_pow, hi.ne, ↓reduceIte,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using e
  · intro H
    ext i
    obtain (hi | hi) := eq_or_ne i ((LinearMap.mul R A) f).charpoly.natDegree
    · simp only [Algebra.coe_lmul_eq_mul, hi, coeff_map, coeff_X_pow, ↓reduceIte]
      rw [← Polynomial.leadingCoeff, ((LinearMap.mul R A) f).charpoly_monic, map_one]
    obtain (hi | hi) := lt_or_gt_of_ne hi
    · simpa [hi.ne, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using H i hi
    · simp [hi.ne', coeff_eq_zero_of_natDegree_lt hi]

lemma exists_image_comap (f : A) (s : Set A) [Module.Free R (A ⧸ Ideal.span s)]
    [Module.Finite R (A ⧸ Ideal.span s)] :
    ∃ t : Finset R,
      comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  classical
  use (Finset.range (Module.finrank R (A ⧸ Ideal.span s))).image
    (Algebra.lmul R (A ⧸ Ideal.span s) (Ideal.Quotient.mk _ f)).charpoly.coeff
  ext x
  rw [mem_image_comap_zeroLocus_sdiff, IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span s),
    isNilpotent_tensor_residueField_iff]
  simp [Set.subset_def]

lemma exists_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    ∃ t : Finset R,
      comap C '' (zeroLocus {g} \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  apply (config := { allowSynthFailures := true }) exists_image_comap
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis

lemma isCompact_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsCompact (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht, ← t.toSet.iUnion_of_singleton_coe, zeroLocus_iUnion, Set.compl_iInter]
  apply isCompact_iUnion
  exact fun _ ↦ by simpa using isCompact_basicOpen _

lemma isOpen_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsOpen (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]
  exact (isClosed_zeroLocus (R := R) t).isOpen_compl

universe u

lemma Polynomial.degree_C_mul_eq_of_mul_ne_zero
    (r : R) (p : R[X]) (h : r * p.leadingCoeff ≠ 0) : (C r * p).degree = p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [degree_eq_natDegree hp, degree_eq_natDegree, natDegree_C_mul_eq_of_mul_ne_zero h]
  exact fun e ↦ h (by simpa using congr(($e).coeff p.natDegree))

lemma Polynomial.monic_unit_leadingCoeff_inv_smul
    (p : R[X]) (h : IsUnit p.leadingCoeff) :
    (C ((h.unit⁻¹ : Rˣ) : R) * p).Monic := by
  nontriviality R
  rw [Monic.def, ← coeff_natDegree, natDegree_C_mul_eq_of_mul_ne_zero, coeff_C_mul,
    coeff_natDegree, IsUnit.val_inv_mul]
  rw [IsUnit.val_inv_mul]
  exact one_ne_zero

lemma Ideal.span_range_update_divByMonic {ι : Type*} [DecidableEq ι]
    (v : ι → R[X]) (i j : ι) (hij : i ≠ j) (h : IsUnit (v i).leadingCoeff) :
    Ideal.span (Set.range (Function.update v j (v j %ₘ (C ((h.unit⁻¹ : Rˣ) : R) * v i)))) =
      Ideal.span (Set.range v) := by
  have H : (C ((h.unit⁻¹ : Rˣ) : R) * v i).Monic :=
    Polynomial.monic_unit_leadingCoeff_inv_smul (v i) h
  refine le_antisymm ?_ ?_ <;>
    simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe]
  · intro k
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_same, modByMonic_eq_sub_mul_div (v j) H]
      apply sub_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ <| Ideal.subset_span ?_))
      · exact ⟨j, rfl⟩
      · exact ⟨i, rfl⟩
    exact Ideal.subset_span ⟨k, (Function.update_noteq (.symm hjk) _ _).symm⟩
  · intro k
    by_cases hjk : j = k
    · subst hjk
      nth_rw 2 [← modByMonic_add_div (v j) H]
      apply add_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ <| Ideal.subset_span ?_))
      · exact ⟨j, Function.update_same _ _ _⟩
      · exact ⟨i, Function.update_noteq hij _ _⟩
    exact Ideal.subset_span ⟨k, Function.update_noteq (.symm hjk) _ _⟩

lemma foo_induction
    (P : ∀ (R : Type u) [CommRing R], Ideal R[X] → Prop)
    (hP₀ : ∀ (R) [CommRing R] (g : R[X]), g.Monic → P R (Ideal.span {g}))
    (hP₁ : ∀ (R) [CommRing R], P R ⊥)
    (hP : ∀ (R) [CommRing R] (c : R) (I : Ideal R[X]),
      P (Localization.Away c) (I.map (mapRingHom (algebraMap _ _))) →
      P (R ⧸ Ideal.span {c}) (I.map (mapRingHom (algebraMap _ _))) → P R I)
    {R} [CommRing R] (I : Ideal R[X]) (hI : I.FG) : P R I := by
  classical
  obtain ⟨n, e, rfl⟩ : ∃ (n : ℕ) (e : Fin (n + 1) → R[X]), I = Ideal.span (Set.range e) := by
    obtain ⟨s, rfl⟩ := hI
    exact ⟨s.card, Fin.cons 0 (Subtype.val ∘ s.equivFin.symm),
      by simp [← Set.union_singleton, Ideal.span_union]⟩
  clear hI
  set v : (Fin (n + 1) → WithBot ℕ) ×ₗ Prop := toLex
    (degree ∘ e, ¬ ∃ i, IsUnit (e i).leadingCoeff ∧ ∀ j, e j ≠ 0 →
      (e i).degree ≤ (e j).degree) with hv
  clear_value v
  induction v using wellFounded_lt (α := (Fin (n + 1) → WithBot ℕ) ×ₗ Prop).induction generalizing R with
  | h v H_IH =>
    by_cases he0 : e = 0
    · rw [he0, Set.range_zero, Ideal.span_singleton_zero]; exact hP₁ R
    cases subsingleton_or_nontrivial R
    · rw [Subsingleton.elim (Ideal.span (Set.range e)) ⊥]; exact hP₁ R
    simp only [funext_iff, Pi.zero_apply, not_forall] at he0
    -- Case I : The `e i ≠ 0` with minimal degree has invertible leading coefficient
    by_cases H : ∃ i, IsUnit (e i).leadingCoeff ∧ ∀ j, e j ≠ 0 → (e i).degree ≤ (e j).degree
    · obtain ⟨i, hi, i_min⟩ := H
      -- Case I.ii : `e j = 0` for all `j ≠ i`.
      by_cases H' : ∀ j ≠ i, e j = 0
      -- then `I = Ideal.span {e i}`
      · convert hP₀ R (C ((hi.unit⁻¹ : Rˣ) : R) * e i) ?_ using 1
        · refine le_antisymm ?_ ?_ <;>
            simp only [Ideal.span_le, Set.range_subset_iff, Set.singleton_subset_iff]
          · intro j
            by_cases hij : i = j
            · simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
              use C (e i).leadingCoeff
              rw [mul_comm, ← mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, one_mul, hij]
            · rw [H' j (.symm hij)]
              exact Ideal.zero_mem _
          · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
        exact Polynomial.monic_unit_leadingCoeff_inv_smul _ _
      -- Case I.i : There is another `e j ≠ 0`
      · simp only [ne_eq, not_forall, Classical.not_imp] at H'
        obtain ⟨j, hj, hj'⟩ := H'
        replace i_min := i_min j hj'
        -- then we can replace `e j` with `e j %ₘ (C h.unit⁻¹ * e i) `
        -- with `h : IsUnit (e i).leadingCoeff`.
        rw [← Ideal.span_range_update_divByMonic e i j (.symm hj) hi]
        refine H_IH _ ?_ _ rfl
        refine .left _ _ (lt_of_le_of_ne (b := (ofLex v).1) ?_ ?_)
        · intro k
          simp only [Function.comp_apply, Function.update_apply, hv, ne_eq, not_exists, not_and,
            not_forall, Classical.not_imp, not_le, ofLex_toLex]
          split_ifs with hjk
          · rw [hjk]
            refine (degree_modByMonic_le _
              (monic_unit_leadingCoeff_inv_smul _ _)).trans
                ((degree_C_mul_eq_of_mul_ne_zero _ _ ?_).trans_le i_min)
            rw [IsUnit.val_inv_mul]
            exact one_ne_zero
          · exact le_rfl
        · simp only [hv, ne_eq, not_exists, not_and, not_forall, not_le, funext_iff,
            Function.comp_apply, exists_prop, ofLex_toLex]
          use j
          simp only [Function.update_same]
          refine ((degree_modByMonic_lt _ (monic_unit_leadingCoeff_inv_smul _ _)).trans_le
            ((degree_C_mul_eq_of_mul_ne_zero _ _ ?_).trans_le i_min)).ne
          rw [IsUnit.val_inv_mul]
          exact one_ne_zero
    -- Case II : The `e i ≠ 0` with minimal degree has non-invertible leading coefficient
    obtain ⟨i, hi, i_min⟩ : ∃ i, e i ≠ 0 ∧ ∀ j, e j ≠ 0 → (e i).degree ≤ (e j).degree := by
      have : ∃ n : ℕ, ∃ i, (e i).degree = n ∧ (e i) ≠ 0 := by
        obtain ⟨i, hi⟩ := he0; exact ⟨(e i).natDegree, i, degree_eq_natDegree hi, hi⟩
      let m := Nat.find this
      obtain ⟨i, hi, hi'⟩ : ∃ i, (e i).degree = m ∧ (e i) ≠ 0 := Nat.find_spec this
      refine ⟨i, hi', fun j hj ↦ ?_⟩
      refine hi.le.trans ?_
      rw [degree_eq_natDegree hj, Nat.cast_le]
      exact Nat.find_min' _ ⟨j, degree_eq_natDegree hj, hj⟩
    have : ¬ IsUnit (e i).leadingCoeff := fun HH ↦ H ⟨i, HH, i_min⟩
    -- We replace `R` by `R ⧸ Ideal.span {(e i).leadingCoeff}` where `(e i).degree` is lowered
    -- and `Localization.Away (e i).leadingCoeff` where `(e i).leadingCoeff` becomes invertible.
    apply hP _ (e i).leadingCoeff
    · rw [Ideal.map_span, ← Set.range_comp]
      refine H_IH _ ?_ _ rfl
      rw [hv, Prod.Lex.lt_iff']
      constructor
      · intro j; simpa using degree_map_le _ _
      simp only [coe_mapRingHom, Function.comp_apply, ne_eq, hv, ofLex_toLex,
        not_exists, not_and, not_forall, Classical.not_imp, not_le, H, not_false_eq_true]
      intro h_eq
      rw [lt_iff_le_not_le]
      simp only [exists_prop, le_Prop_eq, implies_true, true_implies, not_forall, Classical.not_imp,
        not_exists, not_and, not_lt, true_and]
      refine ⟨i, ?_, ?_⟩
      · replace h_eq := congr_fun h_eq i
        simp only [Function.comp_apply] at h_eq
        have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (e i).leadingCoeff)
          (e i).leadingCoeff
        convert this
        nth_rw 2 [← coeff_natDegree]
        rw [natDegree_eq_of_degree_eq h_eq, coeff_map, coeff_natDegree]
      · intro j hj
        refine le_trans ?_ ((i_min j (fun e ↦ hj (by simp [e]))).trans_eq (congr_fun h_eq j).symm)
        simpa using degree_map_le _ _
    · rw [Ideal.map_span, ← Set.range_comp]
      refine H_IH _ ?_ _ rfl
      rw [hv]
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
    exact Ideal.comap_symm (MvPolynomial.isEmptyRingEquiv R (Fin 0))
  | succ n IH =>
    let e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin n) R[X] :=
      (MvPolynomial.renameEquiv R (_root_.finSuccEquiv n)).trans
        (MvPolynomial.optionEquivRight R (Fin n))
    have he : (RingHom.ker (g'.comp <| RingHomClass.toRingHom e.symm)).FG := by
      rw [← RingHom.comap_ker]
      convert hg'.map e.toAlgHom.toRingHom using 1
      exact Ideal.comap_symm e.toRingEquiv
    have := IH (R := R[X]) (S := S) (g'.comp e.symm) (hg.comp e.symm.surjective) he
    convert h₃ _ _ _ _ _ (h₁ _) this using 1
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    congr 1
    ext : 1
    simp [e]

lemma PrimeSpectrum.isRetroCompact_iff {U : Set (PrimeSpectrum R)} (hU : IsOpen U) :
    IsRetroCompact U ↔ IsCompact U := by
  refine isRetroCompact_iff_isCompact_of_isTopologicalBasis _ isTopologicalBasis_basic_opens ?_ hU
  intro i j
  rw [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul]
  exact isCompact_basicOpen _

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

lemma isConstructible_comap_C_zeroLocus_sdiff_zeroLocus {R} [CommRing R]
    (I : Ideal R[X]) (hI : I.FG) (f : R[X]) :
    IsConstructible (comap C '' (zeroLocus I \ zeroLocus {f})) := by
  revert f
  apply foo_induction (hI := hI)
  · intros R _ g hg f
    simp only [zeroLocus_span]
    exact ((isRetroCompact_iff (isOpen_image_comap_of_monic f g hg)).mpr
      (isCompact_image_comap_of_monic f g hg)).isConstructible (isOpen_image_comap_of_monic f g hg)
  · intro R _ f
    simp only [Submodule.bot_coe, zeroLocus_singleton_zero, ← Set.compl_eq_univ_diff,
      ← basicOpen_eq_zeroLocus_compl]
    exact ((isRetroCompact_iff (isOpenMap_comap_C _ (basicOpen f).2)).mpr
      ((isCompact_basicOpen f).image (comap C).2)).isConstructible
      (isOpenMap_comap_C _ (basicOpen f).2)
  · intro R _ c I H₁ H₂ f
    replace H₁ := (H₁ (mapRingHom (algebraMap _ _) f)).image_of_isOpenEmbedding
      _ (localization_away_isOpenEmbedding (Localization.Away c) c)
      (by rw [localization_away_comap_range _ c]
          exact (isRetroCompact_iff (basicOpen c).2).mpr (isCompact_basicOpen c))
    replace H₂ := (H₂ (mapRingHom (Ideal.Quotient.mk _) f)).image_of_isClosedEmbedding
      _ (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective)
      (by rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
          simp only [Ideal.mk_ker, zeroLocus_span, ← basicOpen_eq_zeroLocus_compl]
          exact (isRetroCompact_iff (basicOpen c).2).mpr (isCompact_basicOpen c))
    rw [comap_C_eq_comap_quotient_union_comap_localization _ c]
    simp_rw [Set.preimage_diff, preimage_comap_zeroLocus, Set.image_singleton]
    convert H₂.union H₁ using 5 <;>
      simp only [Ideal.map, zeroLocus_span, coe_mapRingHom, Ideal.Quotient.algebraMap_eq]

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
