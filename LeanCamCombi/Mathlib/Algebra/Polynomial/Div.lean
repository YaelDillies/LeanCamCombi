import Mathlib.Algebra.Polynomial.Div
import LeanCamCombi.Mathlib.Algebra.Order.GroupWithZero.Unbundled

variable {R : Type*} [CommRing R]

namespace Polynomial

local notation "°" => Polynomial.natDegree
local notation "↝" => Polynomial.leadingCoeff
local notation3 "coeff("p")" => Set.range (Polynomial.coeff p)

open Submodule Set Polynomial in
lemma divModByMonicAux_mem_span_coeff_pow : ∀ (p q : R[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i ∈ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ p.natDegree
    ∧
    (p.divModByMonicAux hq).2.coeff i ∈ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ p.natDegree
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i ∈ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ ° p := by
      have H : span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ≤
          span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ ° p := by
        apply le_self_pow₀
        · rw [one_eq_span, span_le, Set.singleton_subset_iff]
          exact subset_span (.inl rfl)
        · positivity
      apply H
      exact subset_span (.inr (.inl ⟨i, rfl⟩))
    split_ifs with hpq
    · simp only [coeff_add, coeff_C_mul, coeff_X_pow]
      generalize hr : (p - q * (C (↝ p) * X ^ (° p - ° q))) = r
      by_cases hr' : r = 0
      · simp only [mul_ite, mul_one, mul_zero, hr', divModByMonicAux, degree_zero,
          le_bot_iff, degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte,
          Prod.mk_zero_zero, Prod.fst_zero, coeff_zero, add_zero, Prod.snd_zero, Submodule.zero_mem,
          and_true]
        split_ifs
        · exact H₀ _
        · exact zero_mem _
      have H : span ℤ coeff(r) ≤ span ℤ coeff(p) ⊔ span ℤ coeff(p) * span ℤ coeff(q) := by
        rw [span_le, ← hr]
        rintro _ ⟨i, rfl⟩
        rw [coeff_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
        apply sub_mem
        · refine SetLike.le_def.mp le_sup_left ?_
          exact subset_span ⟨i, rfl⟩
        · split_ifs
          · rw [mul_comm]
            refine SetLike.le_def.mp le_sup_right (mul_mem_mul ?_ ?_)
            · exact subset_span ⟨_, rfl⟩
            · exact subset_span ⟨_, rfl⟩
          · exact zero_mem _
      have H' : ° r < ° p :=
        natDegree_lt_natDegree hr' (hr ▸ div_wf_lemma hpq hq)
      have H'' : span ℤ ({1} ∪ (coeff(r) ∪ coeff(q))) ^ 2 ^ (° r) ≤
          span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ ° p :=
        calc span ℤ ({1} ∪ (coeff(r) ∪ coeff(q))) ^ 2 ^ (° r)
          _ = (span ℤ {1} ⊔ span ℤ coeff(r) ⊔ span ℤ coeff(q)) ^ 2 ^ (° r) := by
              simp_rw [span_union, sup_assoc]
          _ ≤ (span ℤ {1} ⊔ (span ℤ coeff(p) ⊔ span ℤ coeff(p) * span ℤ coeff(q)) ⊔ span ℤ coeff(q)) ^ 2 ^ (° r) := by gcongr
          _ ≤ ((span ℤ {1} ⊔ span ℤ coeff(p) ⊔ span ℤ coeff(q)) ^ 2) ^ 2 ^ (° r) := by
              gcongr
              rw [pow_two]
              simp only [Submodule.mul_sup, Submodule.sup_mul, ← Submodule.one_eq_span,
                one_mul, mul_one, sup_le_iff]
              refine ⟨⟨by simp only [sup_assoc, le_sup_left], ?_, ?_⟩, ?_⟩
              · apply le_sup_of_le_left
                apply le_sup_of_le_left
                apply le_sup_of_le_left
                exact le_sup_right
              · apply le_sup_of_le_right
                apply le_sup_of_le_left
                exact le_sup_right
              · apply le_sup_of_le_left
                apply le_sup_of_le_left
                exact le_sup_right
          _ = (span ℤ {1} ⊔ span ℤ coeff(p) ⊔ span ℤ coeff(q)) ^ 2 ^ (1 + ° r) := by
              rw [← pow_mul, pow_add 2 1, pow_one]
          _ = span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ (1 + ° r) := by
              simp_rw [span_union, sup_assoc]
          _ ≤ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ ° p := by
              gcongr
              · rw [one_eq_span]
                apply span_mono
                exact Set.subset_union_left
              · exact Nat.le_succ 1
              · exact Nat.one_add_le_iff.mpr H'
      constructor
      · apply add_mem
        · split_ifs <;> simp only [mul_one, mul_zero]
          · exact H₀ _
          · exact zero_mem _
        · exact H'' (divModByMonicAux_mem_span_coeff_pow r _ hq i).1
      · exact H'' (divModByMonicAux_mem_span_coeff_pow _ _ hq i).2
    · constructor
      · simp
      · exact H₀ _
  termination_by p => ° p

open Submodule Set Polynomial in
lemma modByMonic_mem_span_coeff_pow (p q : R[X]) (i) :
    (p %ₘ q).coeff i ∈ span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ p.natDegree := by
  delta modByMonic
  split_ifs with H
  · exact (divModByMonicAux_mem_span_coeff_pow p q H i).2
  · have H : span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ≤
        span ℤ ({1} ∪ (coeff(p) ∪ coeff(q))) ^ 2 ^ ° p := by
      apply le_self_pow₀
      · rw [one_eq_span, span_le, Set.singleton_subset_iff]
        exact subset_span (.inl rfl)
      · positivity
    apply H
    exact subset_span (.inr (.inl ⟨i, rfl⟩))

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
