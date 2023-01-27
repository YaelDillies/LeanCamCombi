import mathlib.measure_theory.measure.measure_space
import probability.probability_mass_function.constructions

open measure_theory
open_locale big_operators classical ennreal nnreal

namespace pmf
variables {α β : Type*}

section of_fintype
variables [fintype α] [fintype β]

open finset

@[simp] lemma map_of_fintype (f : α → ℝ≥0∞) (h : univ.sum (λ (a : α), f a) = 1) (g : α → β) :
  (of_fintype f h).map g = of_fintype (λ b, ∑ a in univ.filter (λ a, g a = b), f a) begin
   have : ((univ : finset β) : set β).pairwise_disjoint
     (λ b, univ.filter $ λ a : α, g a = b),
   { refine λ b₁ _ b₂ _ hb, disjoint_left.2 (λ a ha₁ ha₂, _),
     simp only [mem_filter, mem_univ, true_and] at ha₁ ha₂,
     exact hb (ha₁.symm.trans ha₂) },
   rw ←sum_disj_Union _ _ this,
   convert h,
   exact eq_univ_of_forall (λ a, mem_disj_Union.2 ⟨_, mem_univ _, mem_filter.2 ⟨mem_univ _, rfl⟩⟩),
  end :=
begin
  ext b : 1,
  simp only [sum_filter, eq_comm, map_apply, of_fintype_apply],
  exact tsum_eq_sum (λ _ h, (h $ mem_univ _).elim),
end

end of_fintype

variables [measurable_space α] [measurable_space β] {f : α → β}

lemma to_measure_ne_zero (p : pmf α) : p.to_measure ≠ 0 :=
is_probability_measure.ne_zero p.to_measure

@[simp] lemma map_to_measure (p : pmf α) (hf : measurable f) :
  p.to_measure.map f = (p.map f).to_measure :=
by { ext s hs : 1, rw [pmf.to_measure_map_apply _ _ _ hf hs, measure.map_apply hf hs] }

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

@[simp] lemma map_not_bernoulli' : (bernoulli' p hp).map not = bernoulli' (1 - p) tsub_le_self :=
begin
  have : ∀ p : Prop, finset.univ.filter (λ q : Prop, (¬ q) ↔ p) = {¬ p},
  { rintro p,
    ext q,
    by_cases p; by_cases q; simp [*] },
  refine (map_of_fintype _ _ _).trans _,
  simp only [this, -fintype.univ_Prop, bernoulli', finset.mem_filter, finset.mem_univ, true_and,
    finset.mem_disj_Union, tsub_le_self, eq_iff_iff, finset.sum_singleton, with_top.coe_sub,
    ennreal.coe_one],
  congr' 1 with p,
  rw ennreal.sub_sub_cancel with_top.one_ne_top (ennreal.coe_le_coe.2 hp),
  split_ifs; refl,
end

end bernoulli
end pmf
