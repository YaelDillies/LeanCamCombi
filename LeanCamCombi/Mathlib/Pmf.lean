import Project.Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathbin.Probability.ProbabilityMassFunction.Constructions

#align_import mathlib.pmf

-- TODO: On a countable space, define one-to-one correspondance between `pmf` and probability
-- TODO: On a countable space, define one-to-one correspondance between `pmf` and probability
-- measures
-- measures
open MeasureTheory

open scoped BigOperators Classical ENNReal NNReal

namespace Pmf

variable {α β : Type _}

section OfFintype

variable [Fintype α] [Fintype β]

open Finset

@[simp]
theorem map_ofFintype (f : α → ℝ≥0∞) (h : (univ.Sum fun a : α => f a) = 1) (g : α → β) :
    (ofFintype f h).map g =
      ofFintype (fun b => ∑ a in univ.filterₓ fun a => g a = b, f a)
        (by
          have :
            ((univ : Finset β) : Set β).PairwiseDisjoint fun b =>
              univ.filter fun a : α => g a = b :=
            by
            refine' fun b₁ _ b₂ _ hb => disjoint_left.2 fun a ha₁ ha₂ => _
            simp only [mem_filter, mem_univ, true_and_iff] at ha₁ ha₂ 
            exact hb (ha₁.symm.trans ha₂)
          rw [← sum_disj_Union _ _ this]
          convert h
          exact
            eq_univ_of_forall fun a =>
              mem_disj_Union.2 ⟨_, mem_univ _, mem_filter.2 ⟨mem_univ _, rfl⟩⟩) :=
  by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, of_fintype_apply]
  exact tsum_eq_sum fun _ h => (h <| mem_univ _).elim

end OfFintype

variable [MeasurableSpace α] [MeasurableSpace β] {f : α → β}

theorem toMeasure_ne_zero (p : Pmf α) : p.toMeasure ≠ 0 :=
  IsProbabilityMeasure.ne_zero p.toMeasure

@[simp]
theorem map_toMeasure (p : Pmf α) (hf : Measurable f) : p.toMeasure.map f = (p.map f).toMeasure :=
  by ext s hs : 1; rw [Pmf.toMeasure_map_apply _ _ _ hf hs, measure.map_apply hf hs]

section bernoulli

/-- A `pmf` which assigns probability `p` to true propositions and `1 - p` to false ones. -/
noncomputable def bernoulli' (p : ℝ≥0) (h : p ≤ 1) : Pmf Prop :=
  (ofFintype fun b => if b then p else 1 - p) <| by norm_cast; exact NNReal.eq (by simp [h])

variable {p : ℝ≥0} (hp : p ≤ 1) (b : Prop)

@[simp]
theorem bernoulli'_apply : bernoulli' p hp b = if b then p else 1 - p :=
  rfl

@[simp]
theorem support_bernoulli' : (bernoulli' p hp).support = {b | if b then p ≠ 0 else p ≠ 1} :=
  Set.ext fun b => by by_cases b <;> simp [h, hp.lt_iff_ne]

theorem mem_support_bernoulli'_iff : b ∈ (bernoulli' p hp).support ↔ if b then p ≠ 0 else p ≠ 1 :=
  by simp

@[simp]
theorem map_not_bernoulli' : (bernoulli' p hp).map Not = bernoulli' (1 - p) tsub_le_self :=
  by
  have : ∀ p : Prop, (finset.univ.filter fun q : Prop => ¬q ↔ p) = {¬p} :=
    by
    rintro p
    ext q
    by_cases p <;> by_cases q <;> simp [*]
  refine' (map_of_fintype _ _ _).trans _
  simp only [this, -Fintype.univ_Prop, bernoulli', Finset.mem_filter, Finset.mem_univ, true_and_iff,
    Finset.mem_disjiUnion, tsub_le_self, eq_iff_iff, Finset.sum_singleton, WithTop.coe_sub,
    ENNReal.coe_one]
  congr 1 with p
  rw [ENNReal.sub_sub_cancel WithTop.one_ne_top (ENNReal.coe_le_coe.2 hp)]
  split_ifs <;> rfl

end bernoulli

end Pmf

