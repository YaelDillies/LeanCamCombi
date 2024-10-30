import Mathlib
import LeanCamCombi.Mathlib.Data.Prod.Lex

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

universe u

example {R} (n : ℕ) (f : Fin n → R) (a : R) : Fin (n + 1) → R := Fin.cons a f

@[simp]
lemma Ideal.span_singleton_zero : Ideal.span {0} = (⊥ : Ideal R) := by simp
-- Fin n → ℕ × Prop

lemma foo_induction
    (P : ∀ (R : Type u) [CommRing R], Ideal R[X] → Prop)
    (hP : ∀ (R) [CommRing R] (c : R) (I : Ideal R[X]),
      P (Localization.Away c) (I.map (mapRingHom (algebraMap _ _))) →
      P (R ⧸ Ideal.span {c}) (I.map (mapRingHom (algebraMap _ _))) → P R I)
    (hP₀ : ∀ (R) [CommRing R] (g : R[X]), g.Monic → P R (Ideal.span {g}))
    (hP₁ : ∀ (R) [CommRing R], P R ⊥)
    {R} [CommRing R] (I : Ideal R[X]) (hI : I.FG) : P R I := by
  classical
  obtain ⟨n, e, rfl⟩ : ∃ (n : ℕ) (e : Fin (n + 1) → R[X]), I = Ideal.span (Set.range e) := by
    obtain ⟨s, rfl⟩ := hI
    exact ⟨s.card, Fin.cons 0 (Subtype.val ∘ s.equivFin.symm),
      by simp [← Set.union_singleton, Ideal.span_union]⟩
  clear hI
  set v : Lex ((Fin (n + 1) → ℕ) × ℕ) := toLex
    (natDegree ∘ e, (Finset.univ.filter (fun i ↦ IsUnit (e i).leadingCoeff)).card) with hv
  clear_value v
  have : WellFoundedLT (Lex ((Fin (n + 1) → ℕ) × ℕ)) := inferInstance
  induction v using wellFounded_lt (α := Lex ((Fin (n + 1) → ℕ) × ℕ)).induction generalizing R with
  | h v H_IH =>
    by_cases he0 : e = 0
    · rw [he0, Set.range_zero, Ideal.span_singleton_zero]; exact hP₁ R
    simp only [funext_iff, Pi.zero_apply, not_forall] at he0
    obtain ⟨i, hi, H⟩ : ∃ i, e i ≠ 0 ∧ ∀ j, e j ≠ 0 → (e i).natDegree ≤ (e j).natDegree := by
      have : ∃ n : ℕ, ∃ i, (e i).natDegree = n ∧ (e i) ≠ 0 := by rw [exists_comm]; simpa
      let m := Nat.find this
      obtain ⟨i, hi, hi'⟩ : ∃ i, (e i).natDegree = m ∧ (e i) ≠ 0 := Nat.find_spec this
      exact ⟨i, hi', fun j hj ↦ hi.trans_le (Nat.find_min' _ ⟨j, rfl, hj⟩)⟩
    by_cases hi' : (e i).Monic; swap
    · apply hP _ (e i).leadingCoeff
      · rw [Ideal.map_span, ← Set.range_comp]
        refine H_IH _ ?_ _ rfl
        sorry
      · sorry
    by_cases h' : ∃ j ≠ i, (e j) ≠ 0
    · sorry
    · sorry
