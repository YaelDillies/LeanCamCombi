/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import LeanCamCombi.ConvexityRefactor.StdSimplex

noncomputable section

open Finset Function Set StdSimplex

namespace ConvexityRefactor
variable (R E : Type*) [LinearOrderedSemiring R] [ExistsAddOfLE R] [AddCommMonoid E] [DecidableEq E]
  [Module R E]

class ConvexSpace where
  sConvexComb : StdSimplex E R → E
  segmentMap : R → R → E → E → E
  sConvexComb_single (x : E) : sConvexComb (single x) = x
  sConvexComb_double (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y : E) : sConvexComb (double x y a b ha hb hab) = segmentMap a b x y
  protected sConvexComb_sConvexComb' {ι : Type} {κ : ι → Type} (w : StdSimplex ι R)
    (w' : ∀ i, StdSimplex (κ i) R) (f : ∀ i, κ i → E) :
    sConvexComb (mapDomain (fun i ↦ sConvexComb (mapDomain (f i) (w' i))) w) =
      sConvexComb (mapDomain (fun ⟨i, j⟩ ↦ f i j) $ w.sigma w')

namespace ConvexSpace
variable {R E}
variable [i : ConvexSpace R E] {ι : Type*} {κ : ι → Type*}

def iConvexComb (w : StdSimplex ι R) (f : ι → E) : E := sConvexComb (mapDomain f w)

lemma sConvexComb_mapDomain (w : StdSimplex ι R) (f : ι → E) :
    sConvexComb (mapDomain f w) = iConvexComb w f := rfl

lemma iConvexComb_id (w : StdSimplex E R) : iConvexComb w id = sConvexComb w := by
  simp [iConvexComb]

lemma sConvexComb_sConvexComb (w : StdSimplex ι R) (w' : ∀ i, StdSimplex (κ i) R)
    (f : ∀ i, κ i → E) :
    sConvexComb (mapDomain (fun i ↦ sConvexComb (mapDomain (f i) (w' i))) w) =
      sConvexComb (mapDomain (fun ⟨i, j⟩ ↦ f i j) $ w.sigma w') := by
  simp_rw [← w.mapDomain_shrink, ← (w' _).mapDomain_shrink, ← (w.sigma w').mapDomain_shrink]
  set e := equivShrink.{0} w.support
  set e' := fun i ↦ equivShrink.{0} (w' i).support
  -- simp_rw [← w.mapDomain_restrict, ← (w' _).mapDomain_restrict, ← (w.sigma w').mapDomain_restrict,
  --   ← mapDomain_domCongr _ (equivShrink.{0} w.support),
  --   ← mapDomain_domCongr _ (equivShrink.{0} (w' _).support),
  --   ← mapDomain_domCongr _ (equivShrink.{0} (w.sigma w').support), Function.comp]
  rw [ConvexSpace.sConvexComb_sConvexComb']
  set lhs :=
    mapDomain (
      (fun (⟨i, j⟩ : Σ i, κ i) ↦ f i j) ∘
      (fun (⟨i, j⟩ : Σ i : w.support, (w' i).support) ↦ ⟨i, j⟩) ∘
      (e.symm.sigmaCongr fun i ↦ (e' (e.symm i)).symm))
      (w.shrink.sigma fun i ↦ (w' $ e.symm i).shrink) with lhs_def
  set rhs := mapDomain ((fun ⟨i, j⟩ ↦ f i j) ∘ Subtype.val ∘
    (equivShrink.{0} (w.sigma w').support).symm) (w.sigma w').shrink with rhs_def
  change sConvexComb lhs = sConvexComb rhs
  rw [lhs_def, rhs_def, mapDomain_comp, eq_comm, mapDomain_comp]
  congr!
  rw [shrink, mapDomain_domCongr, mapDomain_subtypeVal_restrict, mapDomain_comp,
    ← domCongr_eq_mapDomain, domCongr_sigma]
  sorry


  -- calc
  --   lhs = mapDomain (fun ⟨i, j⟩ ↦ f i j) (w.sigma w') := by
  --     rw [lhs_def, mapDomain_comp]
  --   _ = mapDomain ((fun ⟨i, j⟩ ↦ f i j) ∘ Subtype.val ∘ (equivShrink.{0} (w.sigma w').support).symm)
  --         (w.sigma w').shrink := by
  --     rw [mapDomain_comp, shrink, mapDomain_domCongr, mapDomain_subtypeVal_restrict]

  -- simp only [toFinsupp_mapDomain, toFinsupp_sigma, smul_eq_mul,
    -- sigma_apply, Finsupp.mapDomain, Finsupp.sum]

  -- have := ConvexSpace.sConvexComb_sConvexComb' (E := E) (self := i)
  --   w.shrink (fun i ↦ (w' _).shrink) _

  -- simp_rw [← w.mapDomain_restrict, ← (w' _).mapDomain_restrict, ← (w.sigma w').mapDomain_restrict,
  --   ← mapDomain_domCongr _ (equivShrink.{0} w.support),
  --   ← mapDomain_domCongr _ (equivShrink.{0} (w' _).support),
  --   ← mapDomain_domCongr _ (equivShrink.{0} (w.sigma w').support), Function.comp]
  -- have := ConvexSpace.sConvexComb_sConvexComb' (E := E)
  --   (domCongr (equivShrink.{0} w.support) w.restrict) (fun i ↦ domCongr (equivShrink.{0} (w' (((equivShrink.{0} w.support) w.restrict)).symm i)).support) (w' _).restrict) _




lemma iConvexComb_iConvexComb (w : StdSimplex ι R) (w' : ∀ i, StdSimplex (κ i) R)
    (f : ∀ i, κ i → E) :
    iConvexComb w (fun i ↦ iConvexComb (w' i) (f i)) =
      iConvexComb (w.sigma w') (fun ⟨i, j⟩ ↦ f i j) := sConvexComb_sConvexComb _ _ _
