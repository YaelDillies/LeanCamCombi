import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Data.Countable.Small
import LeanCamCombi.Mathlib.Data.Finsupp.Order

noncomputable section

open Finset Function

structure StdSimplex (ι R : Type*) [OrderedSemiring R] extends ι →₀ R where
  nonneg' : 0 ≤ toFinsupp
  sum_toFinsupp_eq_one : toFinsupp.sum (fun _ a ↦ a) = 1

namespace StdSimplex
variable {ι R : Type*} [OrderedSemiring R]

@[ext] lemma toFinsupp_injective : Injective (toFinsupp : StdSimplex ι R → ι →₀ R) :=
  fun w w' h ↦ by cases w; cases w'; congr!

instance : FunLike (StdSimplex ι R) ι R where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective.comp toFinsupp_injective

initialize_simps_projections StdSimplex
  (toFun → coe, as_prefix coe, toFun → apply, -apply, as_prefix toFinsupp, as_prefix support)

lemma nonneg (w : StdSimplex ι R) (i : ι) : 0 ≤ w i := w.nonneg' i

attribute [simp] sum_toFinsupp_eq_one

@[simp] lemma sum_support_eq_one (w : StdSimplex ι R) : ∑ i ∈ w.support, w i = 1 :=
  sum_toFinsupp_eq_one _

@[simp] lemma coe_toFinsupp (w : StdSimplex ι R) : ⇑w.toFinsupp = w := rfl

@[simp] lemma coe_mk (w : ι →₀ R) (hw₀ hw₁) : ⇑(mk w hw₀ hw₁) = w := rfl

@[simps! (config := .asFn), simps! apply toFinsupp]
def single (i : ι) : StdSimplex ι R where
  toFinsupp := .single i 1
  nonneg' := by simp
  sum_toFinsupp_eq_one := by simp

@[simps! (config := .asFn), simps! apply toFinsupp]
def double (i j : ι) (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : StdSimplex ι R where
  toFinsupp := .single i a + .single j b
  nonneg' := by apply add_nonneg <;> simpa
  sum_toFinsupp_eq_one := by classical simpa [Finsupp.sum_add_index]

@[simp] lemma double_self (i : ι) (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    double i i a b ha hb hab = single i := by ext : 1; simp [← Finsupp.single_add, hab]

section restrict

@[simps! (config := .asFn), simps! apply toFinsupp]
def restrict (w : StdSimplex ι R) : StdSimplex w.support R where
  toFun i := w i
  support := univ
  mem_support_toFun i := by simpa [-coe_mem] using i.2
  nonneg' i := w.nonneg i
  sum_toFinsupp_eq_one := by simp [Finsupp.sum, sum_attach]

end restrict

section domCongr
variable {κ : Type*}

@[simps!]
def domCongr (e : ι ≃ κ) :  StdSimplex ι R ≃ StdSimplex κ R where
  toFun w :=
    { toFinsupp := .equivCongrLeft e w.toFinsupp
      nonneg' := fun i ↦ w.nonneg _
      sum_toFinsupp_eq_one := by simp }
  invFun w :=
    { toFinsupp := .equivCongrLeft e.symm w.toFinsupp
      nonneg' := fun i ↦ w.nonneg _
      sum_toFinsupp_eq_one := by simp }
  left_inv w := by ext; simp
  right_inv w := by ext; simp

end domCongr

section shrink

@[simps! (config := .asFn), simps! apply toFinsupp]
def shrink (w : StdSimplex ι R) : StdSimplex (Shrink.{0} w.support) R :=
  domCongr (equivShrink.{0} w.support) w.restrict

end shrink

section mapDomain
variable {κ μ : Type*}

@[simps! (config := .asFn) toFinsupp]
def mapDomain (f : ι → κ) (w : StdSimplex ι R) : StdSimplex κ R where
  toFinsupp := w.toFinsupp.mapDomain f
  nonneg' := Finsupp.mapDomain_nonneg w.nonneg'
  sum_toFinsupp_eq_one := by simp [Finsupp.sum_mapDomain_index]

@[simp] lemma mapDomain_id (w : StdSimplex ι R) : mapDomain id w = w := by ext : 1; simp

lemma mapDomain_comp (f : ι → κ) (g : κ → μ) (w : StdSimplex ι R) :
    mapDomain (g ∘ f) w = mapDomain g (mapDomain f w) := by ext : 1; simp [Finsupp.mapDomain_comp]

@[simp] lemma mapDomain_restrict (f : ι → κ) (w : StdSimplex ι R) :
    mapDomain (fun i : w.support ↦ f i) w.restrict = mapDomain f w := by
  ext; simp [Finsupp.mapDomain, Finsupp.sum, ← sum_attach w.support]

@[simp] lemma mapDomain_subtypeVal_restrict (w : StdSimplex ι R) :
    mapDomain Subtype.val w.restrict = w := by
  rw [mapDomain_restrict fun x ↦ x, ← Function.id_def, mapDomain_id]

lemma domCongr_eq_mapDomain (e : ι ≃ κ) (w : StdSimplex ι R) : domCongr e w = mapDomain e w := by
  ext j
  simp [Finsupp.mapDomain, Finsupp.sum]
  rw [sum_eq_single (e.symm j) fun i _ hij ↦ Finsupp.single_eq_of_ne (e.eq_symm_apply.ne.1 hij)]
    <;> simp

lemma mapDomain_domCongr (f : ι → κ) (e : ι ≃ μ) (w : StdSimplex ι R) :
    mapDomain (f ∘ e.symm) (domCongr e w) = mapDomain f w := by
  simp [domCongr_eq_mapDomain, ← mapDomain_comp, Function.comp_assoc]

lemma mapDomain_shrink (f : ι → κ) (w : StdSimplex ι R) :
    mapDomain (fun i ↦ f ((equivShrink.{0} w.support).symm i)) (shrink w) = mapDomain f w := by
  rw [← mapDomain_restrict _ w, ← mapDomain_domCongr _ (equivShrink.{0} w.support) w.restrict]; rfl

end mapDomain

section sigma
variable {ι' S : Type*} {κ : ι → Type*} {κ' : ι' → Type*} [OrderedSemiring S] [Module R S]
  [NoZeroSMulDivisors R S] [OrderedSMul R S]

@[simps! (config := .asFn), simps! apply toFinsupp]
def sigma (w : StdSimplex ι R) (w' : ∀ i, StdSimplex (κ i) S) : StdSimplex (Σ i, κ i) S where
  toFun := fun ⟨i, j⟩ ↦ w i • w' i j
  support := w.support.sigma fun i ↦ (w' i).support
  mem_support_toFun := by simp
  nonneg' := fun ⟨i, j⟩ ↦ smul_nonneg (w.nonneg i) ((w' i).nonneg j)
  sum_toFinsupp_eq_one := by simp [Finsupp.sum, sum_sigma, ← smul_sum, ← sum_smul]

@[simp] lemma domCongr_sigma (f : ι ≃ ι') (g : ∀ i, κ i ≃ κ' (f i)) (w : StdSimplex ι R)
    (w' : ∀ i, StdSimplex (κ i) S) :
    domCongr (f.sigmaCongr g) (w.sigma w') = (domCongr f w).sigma
      fun i ↦ domCongr ((g (f.symm i)).trans (Equiv.cast (by simp))) (w' _) := by
  ext ⟨i', j'⟩
  simp [Equiv.sigmaCongr, Equiv.sigmaCongrLeft, Equiv.sigmaCongrRight, cast]
  congr!
  set i'' := f (f.symm i')
  have h : i'' = i' := f.apply_symm_apply _
  change h ▸ j' = congr_arg κ' h ▸ j'
  clear_value i''
  subst h
  rfl

end sigma
end StdSimplex
