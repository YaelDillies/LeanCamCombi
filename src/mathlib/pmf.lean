import mathlib.fintype
import mathlib.measure
import probability.probability_mass_function.constructions

open measure_theory
open_locale classical nnreal

namespace pmf
variables {α : Type*} [measurable_space α]

lemma to_measure_ne_zero (p : pmf α) : p.to_measure ≠ 0 :=
is_probability_measure.ne_zero p.to_measure

section bernoulli

/-- A `pmf` which assigns probability `p` to true propositions and `1 - p` to false ones. -/
noncomputable def bernoulli' (p : ℝ≥0) (h : p ≤ 1) : pmf Prop :=
of_fintype (λ b, if b then p else 1 - p) $ by { norm_cast, exact nnreal.eq (by simp [h]) }

variables {p : ℝ≥0} (hp : p ≤ 1) (b : Prop)

@[simp] lemma bernoulli'_apply : bernoulli' p hp b = if b then p else 1 - p := rfl

@[simp] lemma support_bernoulli' : (bernoulli' p hp).support = {b | if b then p ≠ 0 else p ≠ 1} :=
set.ext $ λ b, by by_cases b; simp [h, hp.lt_iff_ne]

lemma mem_support_bernoulli'_iff : b ∈ (bernoulli' p hp).support ↔ if b then p ≠ 0 else p ≠ 1 :=
by simp

end bernoulli

end pmf
