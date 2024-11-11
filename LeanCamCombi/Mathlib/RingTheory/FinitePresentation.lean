import Mathlib.RingTheory.FinitePresentation

open Polynomial

universe u v
variable {R : Type u} [CommRing R]

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
