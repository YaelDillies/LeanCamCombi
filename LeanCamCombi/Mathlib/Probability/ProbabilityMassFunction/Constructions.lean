import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# TODO

* On a countable space, define one-to-one correspondance between `PMF` and probability measures
* Make `f` implicit in `toMeasure_map`
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal

namespace PMF
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}

lemma toMeasure_ne_zero (p : PMF α) : p.toMeasure ≠ 0 := IsProbabilityMeasure.ne_zero p.toMeasure

section bernoulli

/-- A `PMF` which assigns probability `p` to true propositions and `1 - p` to false ones. -/
noncomputable def bernoulli' (p : ℝ≥0) (h : p ≤ 1) : PMF Prop :=
  (ofFintype fun b ↦ if b then p else 1 - p) <| by simp_rw [← ENNReal.coe_one, ← ENNReal.coe_sub,
    ← apply_ite ((↑) : ℝ≥0 → ℝ≥0∞), ← ENNReal.coe_finset_sum, ENNReal.coe_inj]; simp [h]

variable {p : ℝ≥0} (hp : p ≤ 1) (b : Prop)

@[simp] lemma bernoulli'_apply : bernoulli' p hp b = if b then (p : ℝ≥0∞) else 1 - p := rfl

@[simp] lemma support_bernoulli' : (bernoulli' p hp).support = {b | if b then p ≠ 0 else p ≠ 1} :=
  Set.ext fun b ↦ by by_cases b <;> simp [*, hp.lt_iff_ne, tsub_eq_zero_iff_le]

lemma mem_support_bernoulli'_iff : b ∈ (bernoulli' p hp).support ↔ if b then p ≠ 0 else p ≠ 1 := by
  simp

@[simp] lemma map_not_bernoulli' : (bernoulli' p hp).map Not = bernoulli' (1 - p) tsub_le_self := by
  have : ∀ p : Prop, ({q | ¬ q ↔ p} : Finset _) = {¬ p} := by
    rintro p
    ext q
    by_cases p <;> by_cases q <;> simp [*]
  refine (map_ofFintype _ _ _).trans ?_
  simp only [eq_iff_iff, this, Finset.sum_singleton, bernoulli']
  congr 1 with q
  split_ifs <;> simp [ENNReal.sub_sub_cancel WithTop.one_ne_top (ENNReal.coe_le_coe.2 hp)]

end bernoulli
end PMF
