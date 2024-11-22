import Mathlib.Algebra.Polynomial.Div
import LeanCamCombi.Mathlib.Algebra.Order.GroupWithZero.Unbundled
import LeanCamCombi.GrowthInGroups.WithBotSucc

variable {R : Type*} [CommRing R]

namespace Polynomial

section mem_pow_natDegree_mul

local notation "°" => Polynomial.natDegree
local notation3 "coeff("p")" => Set.range (coeff p)
local notation3 "submodule("p")" => 1 ⊔ Submodule.span ℤ coeff(p)

attribute [local instance 9999] instPosMulMonoOfMulLeftMono_leanCamCombi instPosMulMonoOfMulLeftMono_leanCamCombi

open Submodule Set in
lemma divModByMonicAux_mem_pow_natDegree_mul : ∀ (p q : R[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i ∈ submodule(q) ^ ° p * submodule(p) ∧
    (p.divModByMonicAux hq).2.coeff i ∈ submodule(q) ^ ° p * submodule(p)
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i ∈ submodule(q) ^ ° p * submodule(p) := by
      refine Submodule.mul_le_mul_left (pow_le_pow_left' le_sup_left (° p)) ?_
      simp only [one_pow, one_mul]
      exact SetLike.le_def.mp le_sup_right (subset_span (mem_range_self i))
    split_ifs with hpq
    · simp only [coeff_add, coeff_C_mul, coeff_X_pow]
      generalize hr : (p - q * (C p.leadingCoeff * X ^ (° p - ° q))) = r
      by_cases hr' : r = 0
      · simp only [mul_ite, mul_one, mul_zero, hr', divModByMonicAux, degree_zero,
          le_bot_iff, degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte,
          Prod.mk_zero_zero, Prod.fst_zero, coeff_zero, add_zero, Prod.snd_zero, Submodule.zero_mem,
          and_true]
        split_ifs
        · exact H₀ _
        · exact zero_mem _
      have H : span ℤ coeff(r) ≤ span ℤ coeff(p) ⊔ span ℤ coeff(q) * span ℤ coeff(p) := by
        rw [span_le, ← hr]
        rintro _ ⟨i, rfl⟩
        rw [coeff_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
        apply sub_mem
        · exact SetLike.le_def.mp le_sup_left (subset_span (mem_range_self _))
        · split_ifs
          · refine SetLike.le_def.mp le_sup_right (mul_mem_mul ?_ ?_) <;> exact subset_span ⟨_, rfl⟩
          · exact zero_mem _
      have H' : ° r < ° p :=
        natDegree_lt_natDegree hr' (hr ▸ div_wf_lemma hpq hq)
      have H'' : submodule(q) ^ ° r * submodule(r) ≤ submodule(q) ^ ° p * submodule(p) := by
        refine (mul_le_mul' le_rfl (sup_le_sup le_rfl H)).trans
          (le_trans ?_ (mul_le_mul' (pow_le_pow_right₀ le_sup_left (Nat.succ_le.mpr H')) le_rfl))
        · rw [pow_succ, mul_assoc]
          gcongr
          simp only [Submodule.mul_sup, Submodule.sup_mul, one_mul, mul_one, sup_le_iff]
          exact ⟨by simp only [sup_assoc, le_sup_left], le_sup_of_le_right le_sup_left,
            by simp only [← sup_assoc, le_sup_right]⟩
      constructor
      · apply add_mem
        · split_ifs <;> simp only [mul_one, mul_zero]
          · exact H₀ _
          · exact zero_mem _
        · exact H'' (divModByMonicAux_mem_pow_natDegree_mul r _ hq i).1
      · exact H'' (divModByMonicAux_mem_pow_natDegree_mul _ _ hq i).2
    · constructor
      · simp
      · exact H₀ _
  termination_by p => ° p

lemma modByMonic_mem_pow_natDegree_mul (p q : R[X]) (i) :
    (p %ₘ q).coeff i ∈ submodule(q) ^ ° p * submodule(p) := by
  delta modByMonic
  split_ifs with H
  · exact (divModByMonicAux_mem_pow_natDegree_mul p q H i).2
  · refine Submodule.mul_le_mul_left (pow_le_pow_left' le_sup_left (° p)) ?_
    simp only [one_pow, one_mul]
    exact SetLike.le_def.mp le_sup_right (Submodule.subset_span (Set.mem_range_self i))

lemma divByMonic_mem_pow_natDegree_mul (p q : R[X]) (i) :
    (p /ₘ q).coeff i ∈ submodule(q) ^ ° p * submodule(p) := by
  delta divByMonic
  split_ifs with H
  · exact (divModByMonicAux_mem_pow_natDegree_mul p q H i).1
  · simp

open Submodule Set Polynomial in
lemma modByMonic_mem_span_coeff_pow' (p q : R[X]) (i) :
    (p %ₘ q).coeff i ∈ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ p.degree.succ := by
  apply modByMonic_mem_pow_natDegree_mul
  sorry

end mem_pow_natDegree_mul

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

end Polynomial
