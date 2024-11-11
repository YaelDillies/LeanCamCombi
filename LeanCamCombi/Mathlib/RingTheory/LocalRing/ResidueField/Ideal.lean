import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

abbrev Ideal.ResidueField (I : Ideal R) [I.IsPrime] : Type _ :=
  LocalRing.ResidueField (Localization.AtPrime I)

instance {R S} [CommRing R] [CommRing S] [LocalRing S] [Algebra R S] :
    Algebra R (LocalRing.ResidueField S) := by infer_instance

@[simp]
lemma LocalRing.algebraMap_residueField [LocalRing R] :
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
