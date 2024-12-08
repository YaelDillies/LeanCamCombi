import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

abbrev Ideal.ResidueField (I : Ideal R) [I.IsPrime] : Type _ :=
  IsLocalRing.ResidueField (Localization.AtPrime I)

instance {R S} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S] :
    Algebra R (IsLocalRing.ResidueField S) := by infer_instance

@[simp]
lemma IsLocalRing.algebraMap_residueField [IsLocalRing R] :
    algebraMap R (IsLocalRing.ResidueField R) = IsLocalRing.residue R := rfl

instance {R₁ R₂ S} [CommRing R₁] [CommRing R₂] [CommRing S] [IsLocalRing S]
    [Algebra R₁ R₂] [Algebra R₁ S] [Algebra R₂ S] [IsScalarTower R₁ R₂ S] :
    IsScalarTower R₁ R₂ (IsLocalRing.ResidueField S) := by
  delta IsLocalRing.ResidueField; infer_instance

noncomputable
abbrev Ideal.residueFieldMap (I : Ideal R) [I.IsPrime] (J : Ideal A) [J.IsPrime]
    (f : R →+* A) (hf : I = J.comap f) : I.ResidueField →+* J.ResidueField :=
  IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)

noncomputable
def Ideal.residueFieldMapₐ (I : Ideal R) [I.IsPrime] (J : Ideal A) [J.IsPrime]
    (hf : I = J.comap (algebraMap R A)) : I.ResidueField →ₐ[R] J.ResidueField where
  __ := Ideal.residueFieldMap I J (algebraMap R A) hf
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I),
      IsLocalRing.algebraMap_residueField]
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
    rfl

@[simp]
lemma Ideal.algebraMap_residueField_eq_zero {I : Ideal R} [I.IsPrime] {x} :
    algebraMap R I.ResidueField x = 0 ↔ x ∈ I := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I),
    IsLocalRing.algebraMap_residueField, IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _

lemma Ideal.ker_algebraMap_residueField (I : Ideal R) [I.IsPrime] :
    RingHom.ker (algebraMap R I.ResidueField) = I := by
  ext x
  exact Ideal.algebraMap_residueField_eq_zero
