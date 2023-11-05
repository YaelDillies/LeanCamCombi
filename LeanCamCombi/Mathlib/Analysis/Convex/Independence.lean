import Mathlib.Analysis.Convex.Independent

/-!
# Convex independence
-/

open Finset

variable {𝕜 E ι : Type*} [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

lemma AffineIndependent.convexIndependent {p : ι → E} (hp : AffineIndependent 𝕜 p) :
    ConvexIndependent 𝕜 p := by
  intro s x hx
  by_contra
  sorry

-- rw [finset.convexHull_eq] at hx,
-- rcases hx with ⟨w, hw₀, hw₁, x_eq⟩,
-- have : s.inj_on p := hp.injective.inj_on _,
-- rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at x_eq,
-- rw finset.sum_image ‹set.inj_on p s› at hw₁,
-- rw finset.sum_image ‹set.inj_on p s› at x_eq,
-- dsimp at hw₁ x_eq,
-- simp only [and_imp, finset.mem_image, forall_apply_eq_imp_iff₂, exists_imp_distrib] at hw₀,
-- let w₀ : ι → ℝ := λ i, if i ∈ s then w (p i) else 0,
-- let w₁ : ι → ℝ := λ i, if x = i then 1 else 0,
-- have thing : _ = _ := unique_combination' (insert x s) hp w₀ w₁ _ _ _ _ (mem_insert_self _ _),
-- { change ite _ _ _ = ite _ _ _ at thing,
--   simpa [h] using thing },
-- { rwa [sum_insert_of_eq_zero_if_not_mem, sum_extend_by_zero s],
--   simp [h] },
-- { simp [sum_ite_eq] },
-- { simpa [sum_insert_of_eq_zero_if_not_mem, h, ite_smul, sum_extend_by_zero s] }
