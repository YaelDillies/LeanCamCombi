import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- TODO: On a countable space, define one-to-one correspondance between `PMF` and probability
-- measures
open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal

namespace PMF
variable {α β : Type*}

section OfFintype
variable [Fintype α] [Fintype β]

open Finset

@[simp]
lemma map_ofFintype (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) (g : α → β) :
    (ofFintype f h).map g =
      ofFintype (fun b ↦ ∑ a in univ.filter fun a ↦ g a = b, f a)
        (by
          have :
            ((univ : Finset β) : Set β).PairwiseDisjoint fun b ↦
              univ.filter fun a : α ↦ g a = b := by
            refine' fun b₁ _ b₂ _ hb ↦ disjoint_left.2 fun a ha₁ ha₂ ↦ _
            simp only [mem_filter, mem_univ, true_and_iff] at ha₁ ha₂
            exact hb (ha₁.symm.trans ha₂)
          rw [← sum_disjiUnion _ _ this]
          convert h
          exact eq_univ_of_forall fun a ↦
            mem_disjiUnion.2 ⟨_, mem_univ _, mem_filter.2 ⟨mem_univ _, rfl⟩⟩) := by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h ↦ (h $ mem_univ _).elim

end OfFintype

variable [MeasurableSpace α] [MeasurableSpace β] {f : α → β}

lemma toMeasure_ne_zero (p : PMF α) : p.toMeasure ≠ 0 := IsProbabilityMeasure.ne_zero p.toMeasure

@[simp]
lemma map_toMeasure (p : PMF α) (hf : Measurable f) : p.toMeasure.map f = (p.map f).toMeasure := by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]

section bernoulli

/-- A `PMF` which assigns probability `p` to true propositions and `1 - p` to false ones. -/
noncomputable def bernoulli' (p : ℝ≥0) (h : p ≤ 1) : PMF Prop :=
  (ofFintype fun b ↦ if b then p else 1 - p) $ by simp_rw [← ENNReal.coe_one, ← ENNReal.coe_sub,
    ← apply_ite ((↑) : ℝ≥0 → ℝ≥0∞), ← ENNReal.coe_finset_sum, ENNReal.coe_inj]; simp [h]

variable {p : ℝ≥0} (hp : p ≤ 1) (b : Prop)

@[simp] lemma bernoulli'_apply : bernoulli' p hp b = if b then (p : ℝ≥0∞) else 1 - p := rfl

@[simp] lemma support_bernoulli' : (bernoulli' p hp).support = {b | if b then p ≠ 0 else p ≠ 1} :=
  Set.ext fun b ↦ by by_cases b <;> simp [*, hp.lt_iff_ne, tsub_eq_zero_iff_le]

lemma mem_support_bernoulli'_iff : b ∈ (bernoulli' p hp).support ↔ if b then p ≠ 0 else p ≠ 1 := by
  simp

@[simp] lemma map_not_bernoulli' : (bernoulli' p hp).map Not = bernoulli' (1 - p) tsub_le_self := by
  have : ∀ p : Prop, (Finset.univ.filter fun q : Prop ↦ ¬ q ↔ p) = {¬ p} := by
    rintro p
    ext q
    by_cases p <;> by_cases q <;> simp [*]
  refine' (map_ofFintype _ _ _).trans _
  simp only [this, bernoulli', Finset.mem_filter, Finset.mem_univ, true_and_iff,
    Finset.mem_disjiUnion, tsub_le_self, eq_iff_iff, Finset.sum_singleton, WithTop.coe_sub,
    ENNReal.coe_one]
  congr 1 with q
  split_ifs <;> simp [ENNReal.sub_sub_cancel WithTop.one_ne_top (ENNReal.coe_le_coe.2 hp)]

end bernoulli
end PMF
